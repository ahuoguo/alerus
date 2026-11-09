// Sampler for the packed DDG encoding: flip(), gen_rand(), load_encoding()
// and sample_encoding() are copied from the POPL'20 artifact
// (experiments/senc.c); main() also writes a histogram.
// usage: gsenc seed steps file.enc B out
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

unsigned long NUM_RNG_CALLS = 0;
static int k = 31;
static int flip_word = 0;
static int flip_pos = 0;
unsigned long NUM_FLIPS = 0;

int gen_rand(void) {
    NUM_RNG_CALLS++;
    return rand();
}

int flip(void){
    NUM_FLIPS++;
    if (flip_pos == 0) {
        flip_word = gen_rand();
        flip_pos = k;
    }
    --flip_pos;
    return (flip_word & (1 << flip_pos)) >> flip_pos;
}

int * load_encoding(char *fname, int *length){
    FILE *file = fopen(fname, "r");
    fscanf(file, "%d", length);
    int *encoding = (int *)malloc((*length) * sizeof(int));
    for(int i = 0; i < (*length); ++i){
        fscanf(file, "%d", &encoding[i]);
    }
    return encoding;
}

int sample_encoding(int *enc){
    int c = 0;
    while (1) {
        int b = flip();
        c = enc[c + b];
        if (enc[c] < 0) {
            return -enc[c];
        }
    }
}

int main(int argc, char **argv){
    int seed = atoi(argv[1]);
    long steps = atol(argv[2]);
    int B = atoi(argv[4]);
    srand(seed);
    int length;
    int *encoding = load_encoding(argv[3], &length);
    long *hist = calloc(2 * B + 1, sizeof(long));
    struct timespec t0, t1;
    clock_gettime(CLOCK_MONOTONIC, &t0);
    for (long i = 0; i < steps; ++i) {
        hist[sample_encoding(encoding) - 1]++;
    }
    clock_gettime(CLOCK_MONOTONIC, &t1);
    double ns = ((t1.tv_sec - t0.tv_sec) * 1e9 + (t1.tv_nsec - t0.tv_nsec)) / steps;
    FILE *f = fopen(argv[5], "w");
    fprintf(f, "ns %f calls %f bits %f\n", ns, (double)NUM_RNG_CALLS / steps, (double)NUM_FLIPS / steps);
    for (int i = 0; i < 2 * B + 1; ++i) if (hist[i]) fprintf(f, "%d %ld\n", i - B, hist[i]);
    fclose(f);
    return 0;
}
