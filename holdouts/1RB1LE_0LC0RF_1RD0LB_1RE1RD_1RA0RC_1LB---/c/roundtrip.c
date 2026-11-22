/* One round trip of a machine on a cell tape, for py/endlaws.py (loaded with ctypes).

   T: 12 transitions (state*2 + read) as (write, move, next), write < 0 for the halting transition.
   The head starts at p in state st and runs until it has been right of `off` and is back left of base + 40.
   Returns 0 when done, 1 on a halt, 2 if the head runs off the right end of the buffer, 3 after maxsteps steps. */
int roundtrip(const int *T, unsigned char *tape, int n, int p, int st, int off, int base, long maxsteps) {
    int went = 0;
    for (long k = 0; k < maxsteps; k++) {
        int i = st * 2 + tape[p];
        if (T[3 * i] < 0) return 1;
        tape[p] = (unsigned char)T[3 * i]; p += T[3 * i + 1]; st = T[3 * i + 2];
        if (p > off) went = 1;
        if (went && p < base + 40) return 0;
        if (p >= n - 5) return 2;
    }
    return 3;
}
