"""The digit map of model.py, accelerated: the effect of the lowest k digits until a wave leaves them is memoized
(like Hashlife), so the run jumps from one visit of the left end of the tape to the next.

exit(k, L): L the lowest k digits (nearest the head first).  Cycles run until a wave passes digit k-1; meanwhile waves
that stop on digit k-1 add to digit k.  Returns (cycles, steps, add, L'): `add` is everything digit k received (the
stops and the passing wave), L' the lowest k digits afterwards.

usage: python3 fast.py EVENTS        the first EVENTS visits of the left end (TWIN=0 for the twin 1RB1RA_1LC0RC_1RE0LD_0RE0LF_1RA---_1RB1LF)
       python3 fast.py check CYCLES  compare with model.py cycle by cycle at every visit, up to CYCLES cycles
"""
import sys
from functools import lru_cache
import model


@lru_cache(maxsize=None)
def exit_(k, L):
    if k == 0:
        return 1, model.CYC, 61, ()
    low, d = L[:k - 1], L[k - 1]
    n = S = add = 0
    while True:
        n1, S1, c1, low = exit_(k - 1, low)
        n += n1
        S += S1
        a = d + c1
        if a % 2:
            j = (a - 3) // 2
            return n, S + model.cost_odd(j), add + j + 1, low + (j + 2,)
        j = (a - 2) // 2
        S += model.cost_even(j, low)
        d = j + 4
        add += j + 1


def left_chain(a, low):
    """The wave value a arriving beyond the last digit (low: all the digits).  (new digits or None, steps)."""
    ps, S = list(low), 0
    while True:
        if a == 1:
            return None, S
        if a % 2:
            j = (a - 3) // 2
            S += model.cost_odd(j)
            ps.append(j + 2)
            a = j + 1
        else:
            j = (a - 2) // 2
            S += model.cost_even(j, ps)
            return ps + [j + 4, j + 1], S


def events(ds, count):
    """Yield (cycles, steps, a0, digits) at each wave reaching beyond the current digits."""
    cyc, steps = 0, model.START
    for _ in range(count):
        n, S, add, low = exit_(len(ds), tuple(ds))
        cyc += n
        steps += S
        new, S2 = left_chain(add, low)
        steps += S2
        yield cyc, steps, add, new
        if new is None:
            return
        ds = new


def main():
    if sys.argv[1] == "check":
        N = int(float(sys.argv[2]))
        ds, steps, i, ev = model.FIRST, model.START, 0, iter(events(model.FIRST, 10 ** 9))
        nxt = next(ev)
        while i < N:
            ds, s, a0 = model.cycle(ds)
            steps += s
            i += 1
            if i == nxt[0]:
                assert (ds, steps) == (nxt[3], nxt[1]), (i, ds, nxt)
                print("ok", i, f"{steps:.3e}")
                nxt = next(ev)
        return
    for cyc, steps, a, new in events(model.FIRST, int(sys.argv[1])):
        t = (a ^ (a + 1)).bit_length() - 1
        print(f"cycles {cyc:.4e}  steps {steps:.4e}  value {a.bit_length()} bits, {t} trailing 1s, "
              f"{'HALT' if new is None else str(len(new)) + ' digits'}", flush=True)


if __name__ == "__main__":
    main()
