"""Check the doubling map of 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- at its left-end visits in state F.

Reads `tmrun MACHINE STEPS at F L K` output on stdin.  The tape right of the head is read as words a = 1100,
b = 110, c = 10 (longest first) and must have the form  c^s MID b^m c c 0 b^j.  For consecutive visits with the same
MID and s going up by 2, it checks that m + j is unchanged and j' = 2 j + c0 with c0 > 0 the same for the whole
phase, and prints each phase.
  ./tmrun 1RB1LF_0RC0RB_0LD1RB_1LE0LB_0LA1LC_0LB--- 5000000000 at F L 5000 | python3 py/phase_check.py
"""
import re
import sys

WORDS = [("1100", "a"), ("110", "b"), ("10", "c")]


def words(cells):
    out, i = "", 0
    while i < len(cells):
        for w, ch in WORDS:
            if cells.startswith(w, i):
                out += ch; i += len(w); break
        else:
            return out, cells[i:]
    return out, ""


def main():
    prev, good, bad, phases = None, 0, 0, []
    for line in sys.stdin:
        p = line.split()
        if p[0] == "running":
            continue
        cells = []
        for tk in p[1:]:
            if ">" in tk:
                head = len(cells); cells.append(tk[-1]); continue
            a, _, e = tk.partition("^")
            cells += [a] * (int(e) if e else 1)
        w, rest = words("".join(cells[head + 1:]))
        m = re.fullmatch(r"(c*)(.*?)(b*)cc", w)
        if not m or not re.fullmatch(r"0(110)*", rest or "0"):
            prev = None; continue
        k, s, mid, b, j = int(p[0]), len(m.group(1)), m.group(2), len(m.group(3)), (len(rest) - 1) // 3 if rest else 0
        if prev and prev[2] == mid and prev[1] + 2 == s:
            c0 = j - 2 * prev[4]
            if phases and phases[-1][0] == mid and phases[-1][4] == prev[0]:
                ok = b + j == prev[3] + prev[4] and c0 == phases[-1][1]
                phases[-1][2].append((b, j)); phases[-1][4] = k
            else:
                ok = b + j == prev[3] + prev[4] and c0 > 0
                phases.append([mid, c0, [(prev[3], prev[4]), (b, j)], prev[0], k])
            good += ok; bad += not ok
            if not ok:
                print("EXCEPTION", prev, (k, s, b, j))
        prev = (k, s, mid, b, j)
    for mid, c0, seq, k0, k1 in phases:
        print(f"phase from step {k0}: c = {c0}, (m, j) = {seq}")
    print("transitions checked", good, "exceptions", bad)


if __name__ == "__main__":
    main()
