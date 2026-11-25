/* open2: open two files named on the command line, report size and the first line of each. Plain C.
   Build: gcc -O2 -static -s -o open2 open2.c    Run: ./open2 FILE_A FILE_B   (exit 0 only if both open) */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int look(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) { perror(path); return 1; }
    fseek(f, 0, SEEK_END);
    long size = ftell(f);
    rewind(f);
    char line[256];
    char *first = fgets(line, sizeof line, f);
    printf("%s: %ld bytes; first line: %s", path, size, first ? line : "(empty)\n");
    if (first && line[0] && line[strlen(line) - 1] != '\n') printf("\n");
    fclose(f);
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 3) { fprintf(stderr, "usage: open2 FILE_A FILE_B\n"); return 2; }
    int a = look(argv[1]);
    int b = look(argv[2]);
    return (a || b) ? 1 : 0;
}
