/* Exhaustive enumeration: every circuit of fan-in-2 AND, OR gates and NOT gates (every gate counted, any number of
   NOT gates) with at most S gates on n <= 7 inputs. Question: is some circuit with <= S gates correct for the Boolean
   sum given by the sets?  Normal form used (loses nothing: a correct circuit with a constant wire or two wires with
   the same function can be shortened and stays correct): no wire is constant, no gate repeats the function of an
   earlier wire; binary gates take inputs a < b.
   For every correct circuit found it reports the size and the number of NOT gates, so the output is, per (size, #NOT),
   the number of correct normal-form circuits, and how many of them have every gate read
   ("nodes" at sizes below S are the search nodes visited after pruning, not all circuits). Serves C4 (task beyond-one-not).
   Build: gcc -O2 -o enum_small enum_small.c     Run: ./enum_small n S "0,1,2;0,3,4" */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef unsigned __int128 T;
static int n, S, m, need; static T M, w[64], outs[16]; static int op[64];
static unsigned long long leaves, hits[16][16], total[16];
static int ga[64], gb[64]; static unsigned long long clean[16][16];
static void rec(int k, int nn, int tn) {           /* k gates placed, nn wires, tn NOT gates */
    int have = 0;
    for (int i = 0; i < m; i++) { for (int j = n; j < nn; j++) if (w[j] == outs[i]) { have++; break; } }
    if (have == m) { hits[k][tn]++;              /* clean = every gate is on a path to an output */
        unsigned long long live = 0;
        for (int i = 0; i < m; i++) for (int j = n; j < nn; j++) if (w[j] == outs[i]) { live |= 1ULL << j; break; }
        for (int j = nn - 1; j >= n; j--) if (live >> j & 1) { live |= 1ULL << ga[j]; live |= 1ULL << gb[j]; }
        int all = 1; for (int j = n; j < nn; j++) if (!(live >> j & 1)) all = 0;
        if (all) clean[k][tn]++; }
    total[k]++;
    if (k == S) { leaves++; return; }
    if (m - have > S - k) return;                   /* each missing output needs its own gate */
    for (int a = 0; a < nn; a++) {
        for (int o = 0; o < 3; o++) {
            for (int b = (o == 2 ? a : a + 1); b < (o == 2 ? a + 1 : nn); b++) {
                T t = o == 2 ? (M ^ w[a]) : (o == 0 ? (w[a] & w[b]) : (w[a] | w[b]));
                if (t == 0 || t == M) continue;
                int dup = 0; for (int j = 0; j < nn; j++) if (w[j] == t) { dup = 1; break; }
                if (dup) continue;
                w[nn] = t; ga[nn] = a; gb[nn] = (o == 2 ? a : b); rec(k + 1, nn + 1, tn + (o == 2));
            }
        }
    }
}
int main(int argc, char **argv) {
    n = atoi(argv[1]); S = atoi(argv[2]); int N = 1 << n; M = 0; for (int x = 0; x < N; x++) M |= (T)1 << x;
    for (int i = 0; i < n; i++) { w[i] = 0; for (int x = 0; x < N; x++) if (x >> i & 1) w[i] |= (T)1 << x; }
    char *s = argv[3]; m = 0; int base = 0; T cur = 0; int sz = 0;
    for (char *p = s;; p++) {
        if (*p >= '0' && *p <= '9') { cur |= w[*p - '0']; sz++; }
        if (*p == ';' || *p == 0) { outs[m++] = cur; base += sz - 1; cur = 0; sz = 0; if (!*p) break; }
    }
    rec(0, n, 0);
    printf("system %s n %d sets %d base %d max gates %d leaves %llu\n", s, n, m, base, S, leaves);
    for (int k = 0; k <= S; k++) { unsigned long long h = 0; for (int t = 0; t < 16; t++) h += hits[k][t];
        printf("  gates %d: nodes %llu, correct %llu", k, total[k], h);
        for (int t = 0; t < 16; t++) if (hits[k][t]) printf("  [%d NOT: %llu]", t, hits[k][t]);
        for (int t = 0; t < 16; t++) if (clean[k][t]) printf("  {every gate read, %d NOT: %llu}", t, clean[k][t]);
        printf("\n"); }
    return 0;
}
