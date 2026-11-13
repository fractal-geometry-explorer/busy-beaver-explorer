"""The pass relation proved in lean/PassRel.lean (`Reach`, `pass_sound`), as a function, compared with the machine.

usage (from the repository root):
    python3 holdouts/1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA/py/passrel.py STEPS

`reach(ks, j)` follows the constructors of `Reach`: sweep over positive digits, bounce at an empty block whose left
neighbour is at least 3 and which is followed by a 1, and stop with `tail`, `zero`, `split`, `split2` or `merge`.  It
returns None where `Reach` has no constructor (left neighbour 2 with a block after the empty block, the wall as left
neighbour, other shapes).  The script runs
the C simulator (c/blkev.c), reads the wall visits (as py/passmap.py does) and counts how many consecutive pairs of
visits are exactly one proved pass.  Lean proves each such pass for all lists; this script only counts how much of
the run they cover.
"""
import collections, os, subprocess, sys, tempfile
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import passmap

M = "1RB0LA_1RC---_0LD1RD_0RA0RE_0RF1RC_1LF0LA"


def reach(ks, j):
    """One pass by the proved relation: (list, tail) -> (list, tail, last rule) or (None, None, reason)."""
    js, i = [], 0
    while True:
        if i == len(ks):
            return (js + [j], 0, "tail") if j >= 1 else (js + [0], 0, "zero")
        if ks[i] > 0:
            js.append(ks[i]); i += 1; continue
        rest = ks[i + 1:]
        if not js:
            return None, None, "empty block at the wall"
        n = js[-1]
        if n == 1:
            if len(js) < 2:
                return None, None, "1 0 at the wall"
            a = js[-2]
            if rest:
                return js[:-2] + [a + 1 + rest[0]] + rest[1:], j, "merge"
            return js[:-2], j + a + 1, "merge"
        if n == 2:
            if not rest and j == 0:
                return js[:-1] + [0, 1, 1], 0, "split2"
            return None, None, "left neighbour 2, a block after the empty block"
        if not rest and j == 0:
            return js[:-1] + [n - 2, 1, 1], 0, "split"
        if rest and rest[0] == 1:
            js = js[:-1] + [n - 2, 1, 2]; i += 2; continue
        return None, None, "other shape after an empty block"


def main(argv):
    steps = int(argv[0])
    exe = os.path.join(tempfile.gettempdir(), "bbx_blkev")
    subprocess.run(["gcc", "-O2", "-o", exe, os.path.join(HERE, "..", "c", "blkev.c")], check=True)
    p = subprocess.Popen([exe, M, str(steps), "D", "1", "1000"], stdout=subprocess.PIPE, text=True)
    prev, cnt = None, collections.Counter()
    for line in p.stdout:
        if "|" not in line:
            continue
        ev = passmap.parse(line, 7)
        if ev is None:
            prev = None; cnt["visits of another shape"] += 1; continue
        if prev is not None:
            cnt["pairs of consecutive visits"] += 1
            k = (ev[1] - prev[1]) // 3      # the wall grows by 3 per pass; the detector can miss a visit
            L, j, why = prev[2], prev[3], ""
            for _ in range(max(k, 1)):
                L, j, why = reach(L, j)
                if L is None:
                    break
            if L is None:
                cnt["not covered: " + why] += 1
            elif (L, j) == (ev[2], ev[3]) and ev[1] - prev[1] == 3 * k and 1 <= k <= 3:
                cnt["one proved pass (ends with " + why + ")" if k == 1 else f"{k} proved passes in a row (visits between them not recorded)"] += 1
            else:
                cnt["MISMATCH"] += 1
        prev = ev
    for k, v in sorted(cnt.items()):
        print(f"{v:10d}  {k}")


if __name__ == "__main__":
    main(sys.argv[1:])
