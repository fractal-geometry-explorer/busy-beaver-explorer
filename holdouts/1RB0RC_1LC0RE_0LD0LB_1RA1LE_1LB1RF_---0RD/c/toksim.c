/* toksim: the token model of 1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD (and of its twin
 * 1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA), the same rules as py/tokens.py and lean/Tokens.lean `next`, in C.
 *
 * A frame is L | R: left word over {0,1,X} (pairs 00, 11 and the mark 0101), right word over {1,0} (pairs 11, 10),
 * the head in state D (twin: A) on a pair 00 between them.  Where no rule applies (the right word used up at the
 * right end of the tape: a "reset") the machine itself is run cell by cell until the next frame, as `stepH` in
 * lean/Sim.lean does.  Step counts are exact (the rules' counts are proved in lean/Rules.lean).
 *
 * usage: toksim [twin] MAXSTEPS [ov]
 *   prints every reset (frame before and after), and with `ov` every overflow (frame with L empty), compressed;
 *   at the end the frame count, the machine steps and the rule counts.
 *        toksim [twin] epoch L R
 *   runs from the frame L | R (L far to near, R near to far, `e` for an empty word) to the end of the first reset
 *   and prints one line: "epoch STEPS OVERFLOWS LBEFORE RBEFORE LAFTER RAFTER RESETSTEPS" (STEPS includes the
 *   reset; words in full, `e` for empty).
 *
 * Arrays: L[0..nl) with L[nl-1] the token next to the head; R[0..nr) with R[nr-1] next to the head.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define CAP (1 << 22)
static char L[CAP], R[CAP];
static long nl, nr;
static long long cnt[8];

/* the machine, for resets */
static int T[6][2][3];
static void parse_machine(const char *m) {
    for (int s = 0; s < 6; s++)
        for (int b = 0; b < 2; b++) {
            const char *p = m + 7 * s + 3 * b;
            if (p[0] == '-') { T[s][b][0] = -1; continue; }
            T[s][b][0] = p[0] - '0'; T[s][b][1] = p[1] == 'R' ? 1 : -1; T[s][b][2] = p[2] - 'A';
        }
}

static void pushL(char c) { L[nl++] = c; }
static void pushR(char c) { R[nr++] = c; }

static void print_frame(FILE *f) {
    /* L far to near, then R near to far, run-length compressed */
    char buf[64];
    long i = 0;
    while (i < nl) {
        long j = i; while (j < nl && L[j] == L[i]) j++;
        if (j - i > 3) { sprintf(buf, "%c^%ld ", L[i], j - i); fputs(buf, f); }
        else for (long k = i; k < j; k++) fputc(L[k], f), fputc(' ', f);
        i = j;
    }
    fputs("| ", f);
    i = nr - 1;
    while (i >= 0) {
        long j = i; while (j >= 0 && R[j] == R[i]) j--;
        if (i - j > 3) fprintf(f, "%c^%ld ", R[i], i - j);
        else for (long k = i; k > j; k--) fputc(R[k], f), fputc(' ', f);
        i = j;
    }
    fputc('\n', f);
}

/* chain: L = rest 0 X (1 X)^j at the top. returns j and sets *restlen (length of rest without the 0), or -1 */
static long chain(long top, long *restlen) {
    long j = 0, i = top;
    while (i >= 2 && L[i - 1] == 'X' && L[i - 2] == '1') { j++; i -= 2; }
    if (i >= 1 && L[i - 1] == 'X' && (i == 1 || L[i - 2] == '0')) { *restlen = i >= 2 ? i - 2 : 0; return j; }
    return -1;
}

/* one rule; returns steps, 0 if none applies */
static long long rule(void) {
    long d = 0;
    while (d < nr && R[nr - 1 - d] == '1') d++;
    if (d == 0) {
        if (nr == 0) return 0;
        long k = 0;
        while (k < nl && L[nl - 1 - k] == '1') k++;
        long rest = nl - k;
        if (rest == 0 || L[rest - 1] == '0') {          /* R1 */
            nl = rest > 0 ? rest - 1 : 0;
            nr--;                                          /* drop the 0 */
            for (long i = 0; i < k + 2; i++) pushR('1');
            cnt[0]++;
            return 4LL * k + 10;
        }
        long rl, j = chain(rest, &rl);
        if (j >= 0) {                                      /* R4 */
            nl = rl;
            nr--;
            for (long i = 0; i < k + 2; i++) pushR('1');
            for (long i = 0; i < j; i++) { pushR('0'); pushR('0'); pushR('1'); }
            pushR('0'); pushR('0');
            cnt[1]++;
            return 8LL * j + 4LL * k + 14;
        }
        return 0;
    }
    if (d + 1 >= nr) return 0;
    char c2 = R[nr - 1 - (d + 1)];
    if (c2 == '0') {                                       /* R2: L | 1^d 0 0 r -> L 1 0^(d-1) X | r */
        nr -= d + 2;
        pushL('1'); for (long i = 0; i < d - 1; i++) pushL('0'); pushL('X');
        cnt[2]++;
        return d == 1 ? 8 : 10LL * d - 2;
    }
    if (d >= 2) {                                          /* R3: L | 1^d 0 1 r -> L 1 0^(d-2) | 0 0 0 r */
        nr -= d + 2;
        pushL('1'); for (long i = 0; i < d - 2; i++) pushL('0');
        pushR('0'); pushR('0'); pushR('0');
        cnt[3]++;
        return d == 2 ? 24 : 10LL * d + 4;
    }
    /* d == 1, R = 1 0 1 r */
    if (nl == 0 || L[nl - 1] == '0') {                     /* R5a */
        if (nl > 0) nl--;
        nr -= 3;
        pushR('0'); pushR('0'); pushR('0'); pushR('1');
        cnt[4]++;
        return 18;
    }
    long rl, j = chain(nl, &rl);
    if (j >= 0) {                                          /* R5 */
        nl = rl;
        nr -= 3;
        pushR('0'); pushR('0'); pushR('0'); pushR('1');
        for (long i = 0; i < j; i++) { pushR('0'); pushR('0'); pushR('1'); }
        pushR('0'); pushR('0');
        cnt[5]++;
        return 8LL * j + 22;
    }
    return 0;
}

/* reset: run the machine from the frame until the next frame. */
static char *tape;
static long long reset(int S) {
    long n = 4 * nl + 2 * nr + 2 + 4000;
    long off = 2000;
    tape = calloc(n + 2 * off, 1);
    long p = off;
    for (long i = 0; i < nl; i++) {
        if (L[i] == '0') { tape[p++] = 0; tape[p++] = 0; }
        else if (L[i] == '1') { tape[p++] = 1; tape[p++] = 1; }
        else { tape[p++] = 0; tape[p++] = 1; tape[p++] = 0; tape[p++] = 1; }
    }
    long pos = p;
    tape[p++] = 0; tape[p++] = 0;
    for (long i = nr - 1; i >= 0; i--) { tape[p++] = 1; tape[p++] = R[i] == '1'; }
    long mn = off, mx = p - 1, st = S;
    for (long long k = 1; k < 100000000; k++) {
        int b = tape[pos];
        if (T[st][b][0] < 0) { printf("HALT in reset after %lld steps\n", k); exit(0); }
        tape[pos] = T[st][b][0]; pos += T[st][b][1]; st = T[st][b][2];
        if (pos < mn) mn = pos;
        if (pos > mx) mx = pos;
        if (pos < 4 || pos > n + 2 * off - 4) { fprintf(stderr, "tape overflow in reset\n"); exit(1); }
        if (st == S && tape[pos] == 0 && tape[pos + 1] == 0) {
            /* parse the right side */
            long i = pos + 2; long r0 = 0; static char RR[CAP]; long nrr = 0;
            while (i <= mx) {
                if (tape[i] == 1 && tape[i + 1] == 1) RR[nrr++] = '1';
                else if (tape[i] == 1 && tape[i + 1] == 0) RR[nrr++] = '0';
                else break;
                i += 2;
            }
            int ok = 1;
            for (long j = i; j <= mx; j++) if (tape[j]) { ok = 0; break; }
            (void)r0;
            if (!ok) continue;
            static char LL[CAP]; long nll = 0;
            i = pos - 1;
            while (i >= mn) {
                if (tape[i - 1] == 1 && tape[i] == 1) { LL[nll++] = '1'; i -= 2; }
                else if (tape[i - 1] == 0 && tape[i] == 0) { LL[nll++] = '0'; i -= 2; }
                else if (tape[i - 1] == 0 && tape[i] == 1 && tape[i - 3] == 0 && tape[i - 2] == 1) { LL[nll++] = 'X'; i -= 4; }
                else { ok = 0; break; }
            }
            if (!ok) continue;
            /* LL is near to far; L wants far..near with leading zeros stripped */
            nl = 0;
            long top = nll - 1;
            while (top >= 0 && LL[top] == '0') top--;
            for (long q = top; q >= 0; q--) L[nl++] = LL[q];
            nr = 0;
            for (long q = nrr - 1; q >= 0; q--) R[nr++] = RR[q];
            free(tape);
            return k;
        }
    }
    fprintf(stderr, "reset did not end\n"); exit(1);
}

static void put_word(void) {
    if (nl == 0) putchar('e');
    for (long i = 0; i < nl; i++) putchar(L[i]);
    putchar(' ');
    if (nr == 0) putchar('e');
    for (long i = nr - 1; i >= 0; i--) putchar(R[i]);
}

static int epoch_mode(int S, const char *ls, const char *rs) {
    nl = nr = 0;
    if (strcmp(ls, "e")) for (const char *c = ls; *c; c++) pushL(*c);
    if (strcmp(rs, "e")) for (long i = (long)strlen(rs) - 1; i >= 0; i--) pushR(rs[i]);
    long long steps = 0, ovs = 0;
    for (;;) {
        long long s = rule();
        if (s == 0) {
            /* keep the frame before the reset, run the reset, print both */
            static char LB[CAP], RB[CAP];
            long nlb = nl, nrb = nr;
            memcpy(LB, L, nl); memcpy(RB, R, nr);
            long long rs_ = reset(S);
            steps += rs_;
            printf("epoch %lld %lld ", steps, ovs);
            if (nlb == 0) putchar('e');
            for (long i = 0; i < nlb; i++) putchar(LB[i]);
            putchar(' ');
            if (nrb == 0) putchar('e');
            for (long i = nrb - 1; i >= 0; i--) putchar(RB[i]);
            putchar(' ');
            put_word();
            printf(" %lld\n", rs_);
            return 0;
        }
        steps += s;
        long z = 0; while (z < nl && L[z] == '0') z++;
        if (z) { memmove(L, L + z, nl - z); nl -= z; }
        if (nl > CAP - 1000 || nr > CAP - 1000) { fprintf(stderr, "word too long\n"); return 1; }
        if (nl == 0) ovs++;
    }
}

int main(int argc, char **argv) {
    int a = 1, twin = 0;
    if (argc > a && !strcmp(argv[a], "twin")) { twin = 1; a++; }
    if (argc > a + 2 && !strcmp(argv[a], "epoch")) {
        parse_machine(twin ? "1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA" : "1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD");
        return epoch_mode(twin ? 0 : 3, argv[a + 1], argv[a + 2]);
    }
    if (argc <= a) { fprintf(stderr, "usage: toksim [twin] MAXSTEPS [ov]\n"); return 1; }
    long long maxsteps = (long long)atof(argv[a]);
    int ov = argc > a + 1 && !strcmp(argv[a + 1], "ov");
    const char *m = twin ? "1RB1LE_1RC0RD_1LD0RE_0LA0LC_1LC1RF_---0RA" : "1RB0RC_1LC0RE_0LD0LB_1RA1LE_1LB1RF_---0RD";
    int S = twin ? 0 : 3;
    parse_machine(m);
    long long steps;
    nl = nr = 0;
    if (twin) steps = 0; else { steps = 5; pushR('0'); pushR('0'); }
    long long frames = 0, resets = 0;
    while (steps < maxsteps) {
        long long s = rule();
        if (s == 0) {
            printf("reset at step %lld: ", steps); print_frame(stdout);
            s = reset(S);
            resets++;
            printf("   after %lld steps: ", s); print_frame(stdout);
            fflush(stdout);
        }
        steps += s; frames++;
        /* strip leading zeros of L (far end) */
        long z = 0; while (z < nl && L[z] == '0') z++;
        if (z) { memmove(L, L + z, nl - z); nl -= z; }
        if (nl > CAP - 1000 || nr > CAP - 1000) { fprintf(stderr, "word too long\n"); return 1; }
        if (ov && nl == 0) { printf("ov %lld: ", steps); print_frame(stdout); fflush(stdout); }
    }
    printf("%lld frames, %lld machine steps, %lld resets; R1 %lld R4 %lld R2 %lld R3 %lld R5a %lld R5 %lld\n",
           frames, steps, resets, cnt[0], cnt[1], cnt[2], cnt[3], cnt[4], cnt[5]);
    printf("last frame: "); print_frame(stdout);
    return 0;
}
