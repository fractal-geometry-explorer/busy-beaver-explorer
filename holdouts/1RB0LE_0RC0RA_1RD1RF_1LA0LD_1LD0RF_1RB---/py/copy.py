"""The copy ticks of 1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---: the left-end ticks whose front ends `| 1`, in which
the head loops between the left end and the block X after the 1 and copies X into a new first block.

usage: ./blocks 1e10 | python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/front.py classify > classify.txt
       python3 holdouts/1RB0LE_0RC0RA_1RD1RF_1LA0LD_1LD0RF_1RB---/py/copy.py TICK < classify.txt
           (TICK: c/tick.c built, e.g. ./tick)

A copy tick reads `P | 1 . X . m1 . ... . mk` (k odd, the m's even, P the blocks before the 1).  For each copy tick
of the run, this script

  * splits the next list into a new first block N, the image P' of P, and the chain m1' ... mk';
  * checks the chain part: m_i' = m_i + (the chain law: from the right +1, +1, -1, +1, -1, ...), and m1 one less;
  * runs the same tick again (c/tick.c, the real machine) with X replaced by X + 2, X + 10, X + 100, and with the
    chain replaced by 100.200.300 and by 4.6.8.10.12, and checks that only N changes, by exactly twice the change
    of X: so N = 2X - c with c and P' functions of P alone (the *rework* of P);
  * prints the table P -> (c, P').

The two copy ticks whose P ends `| 1 | Y` copy Y, not X (N = 2Y + 4, X gains 7, P loses its first two blocks).
"""
import re
import subprocess
import sys
from collections import OrderedDict


def parse(s):
    return list(map(int, re.findall(r"\d+", s))), re.findall(r"[|.]", s)


def fmt(nums, seps):
    out = str(nums[0])
    for s, n in zip(seps, nums[1:]):
        out += s + str(n)
    return out


def chain_law(k):
    """the change of each block of a chain of k blocks in a tick: from the right +1, +1, then -1, +1, -1, ..."""
    return [1 if (k - 1 - t) < 2 else (-1 if (k - 1 - t) % 2 == 0 else 1) for t in range(k)]


def ticks(prog, lists):
    out = subprocess.run([prog] + lists, capture_output=True, text=True, check=True).stdout.split("\n")
    return [ln.split()[0] for ln in out if ln.strip()]


def split(nums, seps):
    """(P nums, P seps, X, m's) of a copy tick list"""
    i = max(j for j in range(len(nums) - 1)
            if nums[j] == 1 and seps[j] == "." and all(s == "." for s in seps[j:]))
    return nums[:i], seps[:max(i - 1, 0)], nums[i + 1], nums[i + 2:]


def decompose(after, k):
    na, sa = parse(after)
    n0, s0 = na[0], (sa[0] if len(sa) else "")
    pa, psa = na[1:len(na) - k], sa[1:len(na) - k - 1]
    ma, msa = na[len(na) - k:], sa[len(na) - k - 1:]
    return n0, s0, pa, psa, ma, msa


def main():
    prog = sys.argv[1]
    lines = [ln.split() for ln in sys.stdin]
    copies, on = [], False
    for ln in lines:
        if ln and ln[0] == "copy":
            on = True
            continue
        if ln and ln[0] == "other":
            break
        if on and len(ln) == 4 and ln[2] == "->":
            copies.append((ln[0], ln[1], ln[3]))
    table = OrderedDict()
    bad = 0
    for step, before, after in copies:
        nb, sb = parse(before)
        P, Ps, X, m = split(nb, sb)
        k = len(m)
        Pstr = fmt(P, Ps) if P else ""
        n0, s0, pa, psa, ma, msa = decompose(after, k)
        law = chain_law(k)
        chain_ok = all(ma[t] == m[t] + law[t] - (1 if t == 0 else 0) for t in range(k)) and all(s == "|" for s in msa)
        # vary X and the chain
        base_tail = "".join("." + str(x) for x in m)
        variants = [(dx, tail) for dx in (2, 10, 100) for tail in (base_tail,)]
        variants += [(0, ".100.200.300"), (0, ".4.6.8.10.12"), (10, ".100.200.300")]
        lists = [(Pstr + "|" if P else "") + "1." + str(X + dx) + tail for dx, tail in variants]
        outs = ticks(prog, lists)
        indep = True
        for (dx, tail), out in zip(variants, outs):
            kk = len(parse(tail)[0])
            o = decompose(out, kk)
            if not (o[0] == n0 + 2 * dx and o[1] == s0 and o[2] == pa and o[3] == psa):
                indep = False
        double = len(P) >= 2 and P[-2] == 1
        key = Pstr
        c = 2 * X - n0
        pimg = (s0 + fmt(pa, psa)) if pa else s0
        e = table.setdefault(key, [0, c, pimg, chain_ok, indep, step, double])
        e[0] += 1
        if (e[1], e[2]) != (c, pimg):
            print(f"DIFFERENT OUTCOME for P = {key} at step {step}")
            bad += 1
        if not double and not (chain_ok and indep):
            print(f"FAIL at step {step}: {before} -> {after} (chain law {chain_ok}, X-independent {indep})")
            bad += 1
    print(f"{len(copies)} copy ticks, {len(table)} different P; {bad} failures\n")
    print("count  P (blocks before the 1)                  c       N | P'   (N = 2X - c)")
    for key, (n, c, pimg, cok, ind, step, double) in table.items():
        note = "   (copies Y, the block between the two 1s: see the docstring)" if double else ""
        print(f"{n:5d}  {key:40s} {c:6d}   N{pimg}{note}")


if __name__ == "__main__":
    main()
