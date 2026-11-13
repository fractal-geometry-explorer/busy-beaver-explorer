"""The first regime of 1RB0LD_0LC0RE_1LA0RD_0RB0LD_1RC1RF_1RA--- as two counters, with exact step counts.

State at an event (head in A on cell 65): H (binary, nb digits), low (binary, w digits), phase (111 or 110), R
(base 3, least significant digit first).  The tape is `1 H 0110 low | phase R 01`, digits as in py/events.py.
Each step of `step()` is one of the rules of lean/Events.lean, with its proved step count.

usage: python3 py/phase1.py EVENTS_FILE FIRST LAST
  EVENTS_FILE: lines `count step lo left | right` (the tape at each event, from /tmp tools `ev2`), FIRST/LAST: the
  event counts to start from and to check up to.  Prints the first mismatch, or OK.
"""
import sys

HD = {"0100": 0, "0101": 1}
LD = {"1000": 0, "1010": 1}
RD = {"001": 0, "011": 1, "010": 2}


def parse(left, right):
    assert left[0] == "1"
    # left = 1 + 4*nb + 4 (marker) + 4*w ; find the marker 0110 scanning from the right in steps of 4
    body = left[1:]
    for w in range(1, len(body) // 4):
        mpos = len(body) - 4 * w - 4
        if body[mpos:mpos + 4] == "0110" and mpos % 4 == 0:
            Hs, Ls = body[:mpos], body[mpos + 4:]
            if all(Hs[i:i + 4] in HD for i in range(0, len(Hs), 4)) and all(Ls[i:i + 4] in LD for i in range(0, len(Ls), 4)):
                break
    else:
        raise ValueError("not a phase-1 tape")
    H = [HD[Hs[i:i + 4]] for i in range(0, len(Hs), 4)][::-1]   # least significant first
    low = [LD[Ls[i:i + 4]] for i in range(0, len(Ls), 4)][::-1]
    ph = right[:3]
    assert right.endswith("01") and (len(right) - 5) % 3 == 0
    R = [RD[right[i:i + 3]] for i in range(3, len(right) - 2, 3)]
    return H, low, ph, R


def render(H, low, ph, R):
    l = "1" + "".join({0: "0100", 1: "0101"}[d] for d in H[::-1]) + "0110" + "".join({0: "1000", 1: "1010"}[d] for d in low[::-1])
    r = ph + "".join({0: "001", 1: "011", 2: "010"}[d] for d in R) + "01"
    return l, r


def add(bits, start, amount_one=True):
    """binary +1 at position `start`; returns (number of ones crossed, overflowed)"""
    i = start
    while i < len(bits) and bits[i] == 1:
        bits[i] = 0
        i += 1
    if i == len(bits):
        return i - start, True
    bits[i] = 1
    return i - start, False


def step(H, low, ph, R):
    """one event; returns the step count (the rule of lean/Events.lean that applies)"""
    if ph == "111":
        n, ovf = add(low, 0)
        newph = "110"
        if not ovf:
            return newph, 12 * n + 12
        base, k_term = 56, 0
    else:
        n, ovf = add(low, 1)
        newph = "111"
        # R + 1
        k = 0
        while k < len(R) and R[k] == 2:
            R[k] = 0
            k += 1
        if k == len(R):
            R.append(0)
            rx = 12
        else:
            rx = 4 * R[k]
            R[k] += 1
        if not ovf:
            return newph, 12 * k + 12 * n + 40 + rx
        base, k_term = 84 + rx, 12 * k
    # low overflow: H + 3
    r = H[0] + 2 * H[1]
    if r == 0:
        H[0] = H[1] = 1
        return newph, base + k_term + 12 * n
    j, hov = add(H, 2)
    if hov:
        raise OverflowError("H overflow (left-end visit)")
    H[0], H[1] = {1: (0, 0), 2: (1, 0), 3: (0, 1)}[r]
    extra = {1: 24, 2: 12, 3: 24}[r]
    return newph, base + extra + k_term + 12 * n + 12 * j


def main():
    f, first, last = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    st = None
    t = None
    for line in open(f):
        c, tt, lo, rest = line.split(None, 3)
        c, tt = int(c), int(tt)
        if c < first:
            continue
        left, right = rest.split()[0], rest.split()[-1]
        if st is None:
            st = list(parse(left, right))
            t = tt
        else:
            if (left, right) != render(*st) or tt != t:
                print("MISMATCH at event", c, "step", tt, "model step", t)
                return
        if c == last:
            print("OK: events", first, "to", last, "steps", t)
            return
        H, low, ph, R = st
        try:
            ph, s = step(H, low, ph, R)
        except OverflowError:
            print("H overflow after event", c, "step", tt)
            return
        st = [H, low, ph, R]
        t += s


if __name__ == "__main__":
    main()
