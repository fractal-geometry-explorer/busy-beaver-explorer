"""Accelerated run from blank tape: fastsim (run-length tape, symtm shift rules) plus the proved `cycle` rule applied
k times at once.  Prints, at each epoch (each time a new long run starts its cycles), the step count, the run list
of the tape (units u^k, long runs as numbers; numbers over 12 digits shown by their digit count) and the residue
mod 3 of the active run.

usage: python3 epochs.py EPOCHS [check]     check: compare the first epochs with the C simulator (../../../tools/c)
"""
import os, sys, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fastsim import Sim

M = "1RB1RE_1LC0LE_1RD0LB_0RA1RC_0RC0RF_1RA---"
LOG = []


def cycle_jump(s):
    """L 1^(a+3) (01)^(b+1) A> 0^inf -> L 1^a (01)^(b+6) A> 0^inf in 6b+45 steps (Rules.lean `cycle`), k times."""
    c = s.cfg
    if c.state != 0 or len(c.right) != 1:
        return False
    L = s.left_segs()
    if len(L) < 2 or L[-1][0] != 'A' or L[-1][1] != 0 or L[-1][2] % 2 or L[-2][0] != 'R' or L[-2][1] != 1:
        return False
    a, B = L[-2][2], L[-1][2] // 2
    if a < 6 or B < 1:
        return False
    k = (a - 3) // 3
    LOG.append((s.steps, a, B, L[:-2]))
    # sum over i < k of 6(B+5i)+39
    s.set(L[:-2] + [('R', 1, a - 3 * k), ('A', 0, 2 * (B + 5 * k))], 0, [], k * (6 * B + 39) + 15 * k * (k - 1))
    return True


def runs_of(segs):
    cells = []
    for t in segs:
        if t[0] == 'R':
            if t[2] > 10**6:
                return None
            cells += [t[1]] * t[2]
        else:
            if t[2] > 10**6:
                return None
            cells += [t[1] ^ (i & 1) for i in range(t[2])]
    return [len(x) for x in ''.join(map(str, cells)).split('0')]


def fmt(n):
    if n.bit_length() > 40:
        return f"[~10^{int(n.bit_length() * 0.30103)}]"
    return str(n)


def show_prefix(segs):
    """The prefix (the tape left of the active run) as a run list: runs of 1s separated by single 0s, u^k for k
    units (runs of length 1), 0 for an empty run (two adjacent 0s)."""
    runs = runs_of(segs)
    if runs is None:
        return "(too long to show)"
    assert runs[-1] == 0, runs     # the prefix ends with the 0 before the active run
    runs = runs[:-1]
    out, i = [], 0
    while i < len(runs):
        if runs[i] == 1:
            j = i
            while j < len(runs) and runs[j] == 1:
                j += 1
            out.append(f"u^{j - i}")
            i = j
        else:
            out.append(str(runs[i]))
            i += 1
    return " ".join(out)


def run(epochs, quiet=False):
    s = Sim(M, [cycle_jump])
    n = 0
    while len(LOG) < epochs and s.halted is None:
        s.move()
        if len(LOG) > n:
            n = len(LOG)
            st, a, B, pre = LOG[-1]
            if not quiet:
                print(f"epoch {n:5d}  step {fmt(st):>14}  runs: {show_prefix(pre)} [{fmt(a)}] u^{B}   (active run mod 3 = {a % 3})", flush=True)
    return s


if __name__ == "__main__":
    epochs = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    s = run(epochs, quiet=len(sys.argv) > 2)
    print("halted:", s.halted, " steps:", fmt(s.steps))
    if len(sys.argv) > 2 and sys.argv[2] == "check":
        # the tape at the start of each epoch, against the C simulator
        here = os.path.dirname(os.path.abspath(__file__))
        exe = os.path.join(here, "tmrun_check")
        src = os.path.join(here, "../../../tools/c/tmrun.c")
        subprocess.run(["gcc", "-O2", "-o", exe, src], check=True)
        for st, a, B, pre in LOG:
            if st > 4 * 10**9:
                break
            out = subprocess.run([exe, M, str(st), "every", str(st)], capture_output=True, text=True).stdout.split("\n")[0]
            tape = out.split(" ", 1)[1].split()
            while tape and tape[0].startswith("0"):
                tape = tape[1:]
            cells = []
            for t in pre + [('R', 1, a), ('A', 0, 2 * B)]:
                cells += [t[1]] * t[2] if t[0] == 'R' else [t[1] ^ (i & 1) for i in range(t[2])]
            exp, i = [], 0
            while i < len(cells):
                j = i
                while j < len(cells) and cells[j] == cells[i]:
                    j += 1
                exp.append(f"{cells[i]}^{j - i}" if j - i > 1 else str(cells[i]))
                i = j
            exp.append("A>0")
            print(st, "C simulator agrees:", tape == exp)
        os.remove(exe)
