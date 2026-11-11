
#import <Foundation/Foundation.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

// Cache only the two inspected ARM64 scanner call sites.
#define BLOCK_SIZE 2048ULL
#define BIT_BYTES (BLOCK_SIZE / 8)
#define CACHE_MAGIC 0x46574332U
#define CACHE_MAX_AGE (12 * 60 * 60)
#define MAX_PATH_BYTES 760
#define MAX_HITS_PER_BLOCK 2048
#define MAX_RECORD_BYTES 2097152
#define MAX_RECORDS 25000

typedef ssize_t (*fsgetpath_func)(
    char *, size_t, fsid_t *, uint64_t
);
extern ssize_t fsgetpath(
    char *, size_t, fsid_t *, uint64_t
);

struct Hit {
    uint16_t offset, length;
    char *path;
    struct Hit *next;
};

struct Chunk {
    int32_t fs0, fs1;
    uint64_t base, when;
    uint8_t seen[BIT_BYTES];
    uint16_t visited, hit_count;
    bool completed, unusable;
    struct Hit *hits;
    struct Chunk *next;
};

struct DiskHeader {
    uint32_t magic, payload_size;
    int32_t fs0, fs1;
    uint64_t base, saved_at;
    uint32_t hit_count, checksum;
};

static struct Chunk *chunks[4096];
static size_t chunk_count;
static pthread_mutex_t mu = PTHREAD_MUTEX_INITIALIZER;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static int cache_fd = -1;
static bool enabled = false;
static fsgetpath_func real_func = NULL;
static char status_file[PATH_MAX];
static uint64_t skipped_calls = 0;

static ssize_t cached_fsgetpath(
    char *, size_t, fsid_t *, uint64_t
);

static ssize_t call_real(
    char *buf, size_t len, fsid_t *fsid, uint64_t ino
) {
    if (real_func && real_func != cached_fsgetpath)
        return real_func(buf, len, fsid, ino);
#ifdef SYS_fsgetpath
    return (ssize_t)syscall(
        SYS_fsgetpath, buf, len, fsid, ino
    );
#else
    errno = ENOSYS;
    return -1;
#endif
}

static void status_report(void) {
    if (!status_file[0]) return;

    char text[256];
    int size = snprintf(
        text, sizeof(text),
        "Filza WQ scan-cache shim loaded.\n"
        "Cached blocks in memory: %zu\n"
        "Avoided fsgetpath calls this launch: %llu\n"
        "To reset: create Documents/"
        "FilzaWQForceFullScan and relaunch.\n",
        chunk_count,
        (unsigned long long)skipped_calls
    );

    if (size < 0) return;

    int fd = open(
        status_file,
        O_CREAT | O_TRUNC | O_WRONLY | O_CLOEXEC,
        0600
    );

    if (fd >= 0) {
        (void)write(fd, text, (size_t)size);
        close(fd);
    }
}

static uint32_t hashbytes(
    const uint8_t *p, size_t n
) {
    uint32_t h = 2166136261U;
    for (size_t i = 0; i < n; ++i)
        h = (h ^ p[i]) * 16777619U;
    return h;
}

static unsigned slot(
    int32_t a, int32_t b, uint64_t base
) {
    uint64_t v = base ^
        ((uint64_t)(uint32_t)a << 21) ^
        (uint32_t)b;

    v ^= v >> 33;
    v *= 0xff51afd7ed558ccdULL;
    v ^= v >> 33;

    return (unsigned)(v & 4095);
}

static struct Chunk *find_chunk(
    int32_t a, int32_t b,
    uint64_t base, bool create
) {
    unsigned s = slot(a, b, base);

    for (struct Chunk *c = chunks[s]; c; c = c->next) {
        if (c->fs0 == a &&
            c->fs1 == b &&
            c->base == base)
            return c;
    }

    if (!create || chunk_count >= MAX_RECORDS)
        return NULL;

    struct Chunk *c = calloc(1, sizeof(*c));
    if (!c) return NULL;

    c->fs0 = a;
    c->fs1 = b;
    c->base = base;
    c->next = chunks[s];
    chunks[s] = c;
    ++chunk_count;

    return c;
}

static struct Hit *find_hit(
    struct Chunk *c, uint16_t offset
) {
    for (struct Hit *h = c->hits; h; h = h->next)
        if (h->offset == offset) return h;

    return NULL;
}

static void add_hit(
    struct Chunk *c,
    uint16_t off,
    const char *path,
    size_t len
) {
    if (c->hit_count >= MAX_HITS_PER_BLOCK) {
        c->unusable = true;
        return;
    }

    if (find_hit(c, off)) return;

    struct Hit *h = calloc(1, sizeof(*h));
    if (!h) {
        c->unusable = true;
        return;
    }

    h->path = malloc(len + 1);
    if (!h->path) {
        free(h);
        c->unusable = true;
        return;
    }

    memcpy(h->path, path, len);
    h->path[len] = 0;
    h->offset = off;
    h->length = (uint16_t)len;
    h->next = c->hits;
    c->hits = h;
    ++c->hit_count;
}

static bool write_all(
    int fd, const void *p, size_t n
) {
    const uint8_t *b = p;

    while (n) {
        ssize_t k = write(fd, b, n);
        if (k <= 0) return false;
        b += k;
        n -= k;
    }

    return true;
}

static void persist_chunk(struct Chunk *c) {
    if (cache_fd < 0 || c->unusable || c->completed)
        return;

    if (lseek(cache_fd, 0, SEEK_END) > 134217728) {
        c->unusable = true;
        return;
    }

    size_t total = 0;

    for (struct Hit *h = c->hits; h; h = h->next)
        total += 4 + h->length;

    if (total > MAX_RECORD_BYTES) {
        c->unusable = true;
        return;
    }

    uint8_t *data = malloc(total ? total : 1);
    if (!data) {
        c->unusable = true;
        return;
    }

    size_t pos = 0;

    for (struct Hit *h = c->hits; h; h = h->next) {
        memcpy(data + pos, &h->offset, 2);
        pos += 2;

        memcpy(data + pos, &h->length, 2);
        pos += 2;

        memcpy(data + pos, h->path, h->length);
        pos += h->length;
    }

    struct DiskHeader head = {0};
    head.magic = CACHE_MAGIC;
    head.payload_size = (uint32_t)total;
    head.fs0 = c->fs0;
    head.fs1 = c->fs1;
    head.base = c->base;
    head.saved_at = (uint64_t)time(NULL);
    head.hit_count = c->hit_count;
    head.checksum = hashbytes(data, total);

    if (write_all(cache_fd, &head, sizeof(head)) &&
        write_all(cache_fd, data, total)) {
        c->when = head.saved_at;
        c->completed = true;
    } else {
        c->unusable = true;
    }

    free(data);
}

static void load_records(void) {
    off_t valid = 0;

    for (size_t rec = 0; rec < MAX_RECORDS; ++rec) {
        struct DiskHeader head;

        if (read(cache_fd, &head, sizeof(head)) !=
            sizeof(head))
            break;

        if (head.magic != CACHE_MAGIC ||
            head.payload_size > MAX_RECORD_BYTES ||
            head.hit_count > MAX_HITS_PER_BLOCK ||
            head.base % BLOCK_SIZE)
            break;

        uint8_t *data = malloc(
            head.payload_size ? head.payload_size : 1
        );
        if (!data) break;

        if (read(cache_fd, data, head.payload_size) !=
                (ssize_t)head.payload_size ||
            hashbytes(data, head.payload_size) !=
                head.checksum) {
            free(data);
            break;
        }

        time_t now = time(NULL);

        if (head.saved_at <= (uint64_t)now &&
            now - head.saved_at < CACHE_MAX_AGE) {

            struct Chunk *c = find_chunk(
                head.fs0, head.fs1, head.base, true
            );

            if (c && !c->completed) {
                size_t pos = 0;
                bool valid_data = true;

                for (uint32_t i = 0;
                     i < head.hit_count; ++i) {
                    uint16_t off, len;

                    if (pos + 4 > head.payload_size) {
                        valid_data = false;
                        break;
                    }

                    memcpy(&off, data + pos, 2);
                    memcpy(&len, data + pos + 2, 2);
                    pos += 4;

                    if (off >= BLOCK_SIZE ||
                        len >= MAX_PATH_BYTES ||
                        pos + len > head.payload_size) {
                        valid_data = false;
                        break;
                    }

                    char path[MAX_PATH_BYTES];
                    memcpy(path, data + pos, len);
                    path[len] = 0;
                    pos += len;

                    if (path[0] != '/') {
                        valid_data = false;
                        break;
                    }

                    add_hit(c, off, path, len);
                }

                if (pos != head.payload_size)
                    valid_data = false;

                if (valid_data && !c->unusable) {
                    c->completed = true;
                    c->when = head.saved_at;
                } else {
                    c->unusable = true;
                }
            }
        }

        free(data);
        valid = lseek(cache_fd, 0, SEEK_CUR);
    }

    ftruncate(cache_fd, valid);
    lseek(cache_fd, 0, SEEK_END);
}

static void initialize(void) {
    real_func = (fsgetpath_func)dlsym(
        RTLD_NEXT, "fsgetpath"
    );

    @autoreleasepool {
        NSString *home = NSHomeDirectory();

        snprintf(
            status_file,
            sizeof(status_file),
            "%s/Documents/FilzaWQCacheStatus.txt",
            home.fileSystemRepresentation
        );

        NSString *dir = [
            home stringByAppendingPathComponent:
            @"Library/Application Support/FilzaWQScanCache"
        ];

        NSString *reset = [
            home stringByAppendingPathComponent:
            @"Documents/FilzaWQForceFullScan"
        ];

        [NSFileManager.defaultManager
            createDirectoryAtPath:dir
            withIntermediateDirectories:YES
            attributes:nil
            error:nil];

        NSString *file = [
            dir stringByAppendingPathComponent:
            @"scan-v2.bin"
        ];

        if ([NSFileManager.defaultManager
                fileExistsAtPath:reset]) {
            unlink(file.fileSystemRepresentation);
            unlink(reset.fileSystemRepresentation);
        }

        cache_fd = open(
            file.fileSystemRepresentation,
            O_CREAT | O_RDWR | O_CLOEXEC,
            0600
        );

        if (cache_fd < 0) return;

        load_records();
        enabled = true;
        status_report();
    }
}

static bool is_filza_scanner(void *return_pc) {
    Dl_info info;

    if (!dladdr(return_pc, &info) ||
        !info.dli_fname || !info.dli_fbase)
        return false;

    if (!strstr(
            info.dli_fname,
            "FilzaApplySandboxExt.dylib"))
        return false;

    uintptr_t offset =
        (uintptr_t)return_pc -
        (uintptr_t)info.dli_fbase;

    return offset == 0x20354 ||
           offset == 0x2089c;
}

static ssize_t cached_fsgetpath(
    char *buf,
    size_t len,
    fsid_t *fsid,
    uint64_t ino
) {
    if (!is_filza_scanner(
            __builtin_return_address(0))) {
        pthread_once(&once, initialize);
        return call_real(buf, len, fsid, ino);
    }

    pthread_once(&once, initialize);

    if (!enabled || !fsid || !buf || len == 0)
        return call_real(buf, len, fsid, ino);

    int32_t a = fsid->val[0];
    int32_t b = fsid->val[1];

    uint64_t base =
        (ino / BLOCK_SIZE) * BLOCK_SIZE;

    uint16_t off = (uint16_t)(ino - base);

    pthread_mutex_lock(&mu);

    struct Chunk *c = find_chunk(
        a, b, base, true
    );

    time_t now = time(NULL);

    bool fast = c &&
        c->completed &&
        !c->unusable &&
        now >= (time_t)c->when &&
        (now - (time_t)c->when) < CACHE_MAX_AGE;

    bool hit = fast &&
        find_hit(c, off) != NULL;

    pthread_mutex_unlock(&mu);

    if (fast && !hit) {
        uint64_t n = __sync_add_and_fetch(
            &skipped_calls, 1
        );

        if ((n & 8191ULL) == 0)
            status_report();

        errno = ENOENT;
        return -1;
    }

    // Positive hits are verified against the real filesystem.
    ssize_t result = call_real(
        buf, len, fsid, ino
    );
    int original_errno = errno;

    if (fast || !c) return result;

    pthread_mutex_lock(&mu);

    c = find_chunk(a, b, base, false);

    if (c && !c->completed && !c->unusable) {
        uint16_t byte = off >> 3;
        uint16_t bit = (uint16_t)(
            1u << (off & 7)
        );

        if (!(c->seen[byte] & bit)) {
            c->seen[byte] |= (uint8_t)bit;
            ++c->visited;
        }

        if (result > 0) {
            size_t n = strnlen(buf, len);

            if (n > 0 &&
                n < MAX_PATH_BYTES &&
                buf[0] == '/') {
                add_hit(c, off, buf, n);
            } else {
                c->unusable = true;
            }
        } else if (original_errno != ENOENT) {
            c->unusable = true;
        }

        if (c->visited == BLOCK_SIZE)
            persist_chunk(c);
    }

    pthread_mutex_unlock(&mu);
    return result;
}

// dyld interposition: only imported fsgetpath calls.
// If unsupported by the runtime, caching remains inactive.
__attribute__((used, section("__DATA,__interpose")))
static const struct {
    const void *replacement;
    const void *original;
} binding = {
    (const void *)&cached_fsgetpath,
    (const void *)&fsgetpath
};
