
#import <Foundation/Foundation.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
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

// These ARM64 caller offsets apply only to the verified base IPA.
#define BLOCK_SIZE 2048ULL
#define CACHE_MAGIC 0x46574333U
#define CACHE_TTL 600
#define MAX_CACHED_PATH 768
#define MAX_RECORDS 25000

typedef ssize_t (*fsgetpath_fn)(
    char *, size_t, fsid_t *, uint64_t
);

extern ssize_t fsgetpath(
    char *, size_t, fsid_t *, uint64_t
);

static ssize_t cached_fsgetpath(
    char *, size_t, fsid_t *, uint64_t
);

typedef struct Hit {
    uint16_t off, len;
    char *path;
    struct Hit *next;
} Hit;

typedef struct Block {
    int32_t a, b;
    uint64_t base, created;
    uint8_t seen[BLOCK_SIZE / 8];
    unsigned count, nhits;
    bool complete, bad;
    Hit *hits;
    struct Block *next;
} Block;

typedef struct Header {
    uint32_t magic, len;
    int32_t a, b;
    uint64_t base, created;
    uint32_t nhits, hash;
} Header;

static Block *blocks[4096];
static size_t nblocks;
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static pthread_once_t once = PTHREAD_ONCE_INIT;
static fsgetpath_fn real_fsgetpath;
static int db = -1;
static bool allow_cached_misses;
static uint64_t saved_calls;

static uint32_t checksum(const void *p, size_t n) {
    const uint8_t *s = p;
    uint32_t v = 2166136261U;
    for (size_t i = 0; i < n; ++i)
        v = (v ^ s[i]) * 16777619U;
    return v;
}

static unsigned bucket(
    int32_t a, int32_t b, uint64_t base
) {
    uint64_t x =
        base ^ ((uint64_t)(uint32_t)a << 32) ^
        (uint32_t)b;

    x ^= x >> 33;
    x *= 0xff51afd7ed558ccdULL;

    return (unsigned)((x ^ (x >> 33)) & 4095);
}

static Block *find_block(
    int32_t a, int32_t b, uint64_t base, bool create
) {
    unsigned i = bucket(a, b, base);

    for (Block *p = blocks[i]; p; p = p->next)
        if (p->a == a && p->b == b && p->base == base)
            return p;

    if (!create || nblocks >= MAX_RECORDS)
        return NULL;

    Block *p = calloc(1, sizeof(*p));
    if (!p) return NULL;

    p->a = a;
    p->b = b;
    p->base = base;
    p->next = blocks[i];
    blocks[i] = p;
    ++nblocks;

    return p;
}

static Hit *find_hit(Block *p, uint16_t off) {
    for (Hit *h = p->hits; h; h = h->next)
        if (h->off == off) return h;

    return NULL;
}

static void add_hit(
    Block *p, uint16_t off, const char *s, size_t len
) {
    if (
        len == 0 || len >= MAX_CACHED_PATH ||
        s[0] != '/' || p->nhits >= BLOCK_SIZE
    ) {
        p->bad = true;
        return;
    }

    if (find_hit(p, off)) return;

    Hit *h = calloc(1, sizeof(*h));
    if (!h) {
        p->bad = true;
        return;
    }

    h->path = malloc(len + 1);
    if (!h->path) {
        free(h);
        p->bad = true;
        return;
    }

    memcpy(h->path, s, len);
    h->path[len] = 0;
    h->off = off;
    h->len = (uint16_t)len;
    h->next = p->hits;
    p->hits = h;
    ++p->nhits;
}

static bool write_all(
    int fd, const void *p, size_t n
) {
    const uint8_t *s = p;

    while (n) {
        ssize_t k = write(fd, s, n);
        if (k <= 0) return false;

        s += k;
        n -= (size_t)k;
    }

    return true;
}

static void store(Block *p) {
    if (db < 0 || p->bad || p->complete)
        return;

    size_t n = 0;

    for (Hit *h = p->hits; h; h = h->next)
        n += 4 + h->len;

    if (n > 2097152) {
        p->bad = true;
        return;
    }

    uint8_t *payload = malloc(n ? n : 1);
    if (!payload) {
        p->bad = true;
        return;
    }

    size_t pos = 0;

    for (Hit *h = p->hits; h; h = h->next) {
        memcpy(payload + pos, &h->off, 2);
        pos += 2;

        memcpy(payload + pos, &h->len, 2);
        pos += 2;

        memcpy(payload + pos, h->path, h->len);
        pos += h->len;
    }

    Header head = {0};
    head.magic = CACHE_MAGIC;
    head.len = (uint32_t)n;
    head.a = p->a;
    head.b = p->b;
    head.base = p->base;
    head.created = (uint64_t)time(NULL);
    head.nhits = p->nhits;
    head.hash = checksum(payload, n);

    if (
        lseek(db, 0, SEEK_END) > 134217728 ||
        !write_all(db, &head, sizeof(head)) ||
        !write_all(db, payload, n)
    ) {
        p->bad = true;
    } else {
        p->complete = true;
        p->created = head.created;
    }

    free(payload);
}

static void load(void) {
    off_t good = 0;
    time_t now = time(NULL);

    for (int i = 0; i < MAX_RECORDS; i++) {
        Header h = {0};

        if (read(db, &h, sizeof(h)) != sizeof(h))
            break;

        if (
            h.magic != CACHE_MAGIC ||
            h.len > 2097152 ||
            h.nhits > BLOCK_SIZE ||
            h.base % BLOCK_SIZE
        ) break;

        uint8_t *buf = malloc(h.len ? h.len : 1);
        if (!buf) break;

        if (
            read(db, buf, h.len) != (ssize_t)h.len ||
            checksum(buf, h.len) != h.hash
        ) {
            free(buf);
            break;
        }

        if (
            h.created <= (uint64_t)now &&
            now - (time_t)h.created < CACHE_TTL
        ) {
            Block *p = find_block(
                h.a, h.b, h.base, true
            );

            if (p && !p->complete) {
                size_t pos = 0;
                bool ok = true;

                for (unsigned j = 0; j < h.nhits; j++) {
                    uint16_t off, len;

                    if (pos + 4 > h.len) {
                        ok = false;
                        break;
                    }

                    memcpy(&off, buf + pos, 2);
                    memcpy(&len, buf + pos + 2, 2);
                    pos += 4;

                    if (
                        off >= BLOCK_SIZE ||
                        len == 0 ||
                        len >= MAX_CACHED_PATH ||
                        pos + len > h.len
                    ) {
                        ok = false;
                        break;
                    }

                    char path[MAX_CACHED_PATH];
                    memcpy(path, buf + pos, len);
                    path[len] = 0;
                    pos += len;

                    add_hit(p, off, path, len);
                }

                if (pos != h.len) ok = false;

                if (ok && !p->bad) {
                    p->complete = true;
                    p->created = h.created;
                } else {
                    p->bad = true;
                }
            }
        }

        free(buf);
        good = lseek(db, 0, SEEK_CUR);
    }

    ftruncate(db, good);
    lseek(db, 0, SEEK_END);
}

// Missing or empty generated directories mean the previous
// container discovery did NOT complete successfully.
static bool populated_catalog(void) {
    @autoreleasepool {
        NSFileManager *fm =
            [NSFileManager defaultManager];

        NSString *root = [
            NSHomeDirectory()
            stringByAppendingPathComponent:
            @"Documents/worse_query"
        ];

        NSArray *expected = @[
            @"App Data (by app)",
            @"App Data (UUID)",
            @"App Groups",
            @"System Data",
            @"Extension Data (containers)",
            @"Internal Daemon Data (containers)",
            @"System Groups (containers)",
            @"App Data (apps)"
        ];

        NSUInteger found = 0;

        for (NSString *name in expected) {
            BOOL isDir = NO;

            if (
                [fm fileExistsAtPath:
                    [root stringByAppendingPathComponent:name]
                    isDirectory:&isDir] && isDir
            ) {
                ++found;
            }
        }

        if (found < 6)
            return false;

        for (NSString *name in @[
            @"App Data (by app)",
            @"App Data (UUID)"
        ]) {
            NSString *path = [
                root stringByAppendingPathComponent:name
            ];

            NSArray *items = [
                fm contentsOfDirectoryAtPath:path
                error:NULL
            ];

            if (items.count > 0)
                return true;
        }

        return false;
    }
}

static void status(void) {
    @autoreleasepool {
        NSString *path = [
            NSHomeDirectory()
            stringByAppendingPathComponent:
            @"Documents/FilzaWQCacheStatus.txt"
        ];

        NSString *msg = [
            NSString stringWithFormat:
            @"WQ cache v3\n"
            @"Verified previous catalog: %@\n"
            @"Blocks: %zu\n"
            @"Skipped inode lookups: %llu\n",
            allow_cached_misses ? @"YES" : @"NO",
            nblocks,
            (unsigned long long)saved_calls
        ];

        [msg
            writeToFile:path
            atomically:YES
            encoding:NSUTF8StringEncoding
            error:NULL];
    }
}

static void initialize(void) {
    real_fsgetpath = (fsgetpath_fn)dlsym(
        RTLD_NEXT, "fsgetpath"
    );

    @autoreleasepool {
        // An incomplete first launch always scans normally.
        allow_cached_misses = populated_catalog();

        NSString *dir = [
            NSHomeDirectory()
            stringByAppendingPathComponent:
            @"Library/Application Support/FilzaWQScanCache"
        ];

        [[NSFileManager defaultManager]
            createDirectoryAtPath:dir
            withIntermediateDirectories:YES
            attributes:nil
            error:NULL];

        NSString *path = [
            dir stringByAppendingPathComponent:
            @"scan-v3.bin"
        ];

        NSString *reset = [
            NSHomeDirectory()
            stringByAppendingPathComponent:
            @"Documents/FilzaWQForceFullScan"
        ];

        if (
            [[NSFileManager defaultManager]
                fileExistsAtPath:reset]
        ) {
            unlink(path.fileSystemRepresentation);
            unlink(reset.fileSystemRepresentation);
            allow_cached_misses = false;
        }

        db = open(
            path.fileSystemRepresentation,
            O_CREAT | O_RDWR | O_CLOEXEC,
            0600
        );

        if (db >= 0) load();
        status();
    }
}

static ssize_t original(
    char *buf, size_t size, fsid_t *fs, uint64_t ino
) {
    fsgetpath_fn fn = real_fsgetpath;

    if (!fn || fn == cached_fsgetpath)
        fn = (fsgetpath_fn)dlsym(
            RTLD_NEXT, "fsgetpath"
        );

    if (fn && fn != cached_fsgetpath)
        return fn(buf, size, fs, ino);

#ifdef SYS_fsgetpath
    return (ssize_t)syscall(
        SYS_fsgetpath, buf, size, fs, ino
    );
#else
    errno = ENOSYS;
    return -1;
#endif
}

static bool scanner_caller(void *pc) {
    Dl_info info;

    if (
        !dladdr(pc, &info) ||
        !info.dli_fname ||
        !info.dli_fbase ||
        !strstr(
            info.dli_fname,
            "FilzaApplySandboxExt.dylib"
        )
    ) {
        return false;
    }

    uintptr_t off =
        (uintptr_t)pc -
        (uintptr_t)info.dli_fbase;

    return off == 0x20354 || off == 0x2089c;
}

static ssize_t cached_fsgetpath(
    char *buf, size_t size, fsid_t *fs, uint64_t ino
) {
    bool scanner = scanner_caller(
        __builtin_return_address(0)
    );

    if (!scanner)
        return original(buf, size, fs, ino);

    pthread_once(&once, initialize);

    if (!fs || !buf || size == 0 || db < 0)
        return original(buf, size, fs, ino);

    uint64_t base =
        (ino / BLOCK_SIZE) * BLOCK_SIZE;

    uint16_t off = (uint16_t)(ino - base);

    pthread_mutex_lock(&lock);

    Block *p = find_block(
        fs->val[0], fs->val[1], base, true
    );

    bool active =
        allow_cached_misses &&
        p && p->complete && !p->bad &&
        (time(NULL) - (time_t)p->created) < CACHE_TTL;

    bool hit =
        active && find_hit(p, off) != NULL;

    pthread_mutex_unlock(&lock);

    if (active && !hit) {
        uint64_t n = __sync_add_and_fetch(
            &saved_calls, 1
        );

        if ((n & 8191ULL) == 0)
            status();

        errno = ENOENT;
        return -1;
    }

    ssize_t rc = original(
        buf, size, fs, ino
    );

    int err = errno;

    if (!p || active) {
        errno = err;
        return rc;
    }

    pthread_mutex_lock(&lock);

    p = find_block(
        fs->val[0], fs->val[1], base, false
    );

    if (p && !p->complete && !p->bad) {
        unsigned byte = off >> 3;
        unsigned mask = 1U << (off & 7);

        if (!(p->seen[byte] & mask)) {
            p->seen[byte] |= (uint8_t)mask;
            ++p->count;
        }

        if (rc > 0) {
            size_t n = strnlen(buf, size);

            if (
                n > 0 &&
                n < MAX_CACHED_PATH &&
                buf[0] == '/'
            ) {
                add_hit(p, off, buf, n);
            } else {
                p->bad = true;
            }
        } else if (err != ENOENT) {
            p->bad = true;
        }

        if (p->count == BLOCK_SIZE)
            store(p);
    }

    pthread_mutex_unlock(&lock);

    errno = err;
    return rc;
}

// Retain the original system function for non-scanner calls.
// Dyld interposition may vary with iOS signing/runtime rules.
__attribute__((used, section("__DATA,__interpose")))
static const struct {
    const void *replacement, *original;
} interpose_entry = {
    (const void *)&cached_fsgetpath,
    (const void *)&fsgetpath
};
