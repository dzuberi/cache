#ifdef CCOMPILER
#include <stdio.h>
#include <inttypes.h>
#include <stdlib.h>
#include <string.h>
#else
#include <cstdio>
#include <cinttypes>
#include <cstdlib>
#include <cstring>
#endif

#include <unistd.h>
#include "cachesim.hpp"

void print_help_and_exit(void) {
    printf("cachesim [OPTIONS] < traces/file.trace\n");
    printf("-h\t\tThis helpful output\n");
    printf("L1 parameters:\n");
    printf("  -c C1\t\tTotal size in bytes is 2^C1\n");
    printf("  -b B1\t\tSize of each block in bytes is 2^B1\n");
    printf("  -s S1\t\tNumber of blocks per set is 2^S1\n");
    printf("  -t T1\t\tPrefetcher type. Valid values are 0-3\n");
    printf("  -p P1\t\tMarkov table rows\n");
    exit(0);
}

void print_statistics(cache_stats_t* p_stats);

int main(int argc, char* argv[]) {
    int opt;
    uint64_t c1 = DEFAULT_C1;
    uint64_t b1 = DEFAULT_B1;
    uint64_t s1 = DEFAULT_S1;
    uint64_t p1 = DEFAULT_P1;
    uint64_t prefetcher_type = DEFAULT_T;

    /* Read arguments */
    while(-1 != (opt = getopt(argc, argv, "c:b:s:p:t:h"))) {
        switch(opt) {
        case 'c':
            c1 = atoi(optarg);
            break;
        case 'b':
            b1 = atoi(optarg);
            break;
        case 's':
            s1 = atoi(optarg);
            break;
        case 'p':
            p1 = atoi(optarg);
            break;
        case 't':
            prefetcher_type = atoi(optarg);
            break;
        case 'h':
            /* Fall through */
        default:
            print_help_and_exit();
            break;
        }
    }

    printf("Cache Settings\n");
    printf("c: %" PRIu64 "\n", c1);
    printf("b: %" PRIu64 "\n", b1);
    printf("s: %" PRIu64 "\n", s1);
    printf("t: %" PRIu64 "\n", prefetcher_type);
    printf("p: %" PRIu64 "\n", p1);
    printf("\n");

    /* Setup the cache */
    setup_cache(c1, b1, s1, p1, prefetcher_type);

    /* Setup statistics */
    cache_stats_t stats;
    memset(&stats, 0, sizeof(cache_stats_t));

    /* Begin reading the file */
    char rw;
    uint64_t address;
    while (!feof(stdin)) {
        int ret = fscanf(stdin, "%c %" PRIx64 "\n", &rw, &address);
        if(ret == 2) {
            cache_access(rw, address, &stats);
        }
    }

    complete_cache(&stats);

    print_statistics(&stats);

    return 0;
}

void print_statistics(cache_stats_t* p_stats) {
    printf("Cache Statistics\n");
    printf("Accesses: %" PRIu64 "\n", p_stats->accesses);
    printf("L1 hits: %" PRIu64 "\n", p_stats->total_hits_l1);
    printf("L1 misses: %" PRIu64 "\n", p_stats->total_misses_l1);
    printf("Hit ratio for L1: %.3f\n", p_stats->l1_hit_ratio);
    printf("Miss ratio for L1: %.3f\n", p_stats->l1_miss_ratio);
    printf("Reads: %" PRIu64 "\n", p_stats->reads);
    printf("Read hits to L1: %" PRIu64 "\n", p_stats->read_hits_l1);
    printf("Read misses to L1: %" PRIu64 "\n", p_stats->read_misses_l1);
    printf("Read hit ratio for L1: %.3f\n", p_stats->read_hit_ratio);
    printf("Read miss ratio for L1: %.3f\n", p_stats->read_miss_ratio);
    printf("Writes: %" PRIu64 "\n", p_stats->writes);
    printf("Write hits to L1: %" PRIu64 "\n", p_stats->write_hits_l1);
    printf("Write misses to L1: %" PRIu64 "\n", p_stats->write_misses_l1);
    printf("Write backs from L1: %" PRIu64 "\n", p_stats->write_back_l1);
    printf("Write hit ratio for L1: %.3f\n", p_stats->write_hit_ratio);
    printf("Write miss ratio for L1: %.3f\n", p_stats->write_miss_ratio);
    printf("Prefetcher Statistics\n");
    printf("Prefetch issued: %" PRIu64 "\n", p_stats->prefetch_issued);
    printf("Prefetch hits: %" PRIu64 "\n", p_stats->prefetch_hits);
    printf("Prefetch hit ratio: %.3f\n", p_stats->prefetch_hit_ratio);
    printf("Prefetch buffer misses: %" PRIu64 "\n", p_stats->prefetch_misses);
    printf("Overall miss ratio for AAT calculation: %.3f\n", p_stats->overall_miss_ratio);
    printf("Average access time (AAT): %.3f\n", p_stats->avg_access_time_l1);
}

