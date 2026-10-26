"""Closure check: every proven macro step maps a canonical configuration to a canonical configuration.

Canonical configuration: blank tape, content (from the first 1 to the last 1) whose maximal runs are
  00 wall, 000 gap, 11 marker, 111 block (no longer runs), with the head either
  - gap phase: state E on the last 0 of a gap, or E on the third 0 of 0000 (a gap meeting a wall), or
  - packet phase: state A on a 1 followed by 1; the content with those two cells removed is canonical.
Invariants: J no block left of the head; K no gap right of the head; A no wall directly followed by a marker.

Each theorem is checked for stripe counts m, j in 0..3 (longer stripes only lengthen alternating stretches,
which never touch a run) and for every 6-cell tape just outside the pattern on each side (or blank tape there).
Cells further out are never read or changed, so their runs and invariants carry over unchanged."""
import itertools, sys
from symtm import tokens, Lin, Rep, Ctx, Blank
import proofs

HL, HR, BL, BR = "HL", "HR", "BL", "BR"

def expand(side, ctxL, ctxR, v):
    out = []
    for part in side.split(" | "):
        if part.strip() == "0^inf":
            out.append("BLANK"); continue
        for t in tokens(part, **{k: Lin(x) for k, x in v.items()}):
            if t == Ctx("L"): out.extend(ctxL)
            elif t == Ctx("R"): out.extend(ctxR)
            elif isinstance(t, Rep): out.extend(list(t.word) * t.n.k)
            else: out.append(t)
    return out

def window(pat, ctxL, ctxR, v):
    left = expand(pat[0], ctxL, ctxR, v); right = expand(pat[2], ctxL, ctxR, v)
    left = [BL if c == "BLANK" else c for c in left]; right = [BR if c == "BLANK" else c for c in right]
    return left + right, len(left), pat[1]

def runs(cells):
    """Maximal runs of 0s/1s among known cells: (symbol, start, end, partial) ; partial = touches hidden tape."""
    out = []; i = 0
    while i < len(cells):
        c = cells[i]
        if c in (0, 1):
            j = i
            while j + 1 < len(cells) and cells[j + 1] == c: j += 1
            partial = (i > 0 and cells[i - 1] == HL) or (j + 1 < len(cells) and cells[j + 1] == HR)
            blank = (c == 0) and ((i > 0 and cells[i - 1] == BL) or (j + 1 < len(cells) and cells[j + 1] == BR))
            out.append((c, i, j, partial, blank))
            i = j + 1
        else:
            i += 1
    return out

def check(cells, h, state, allow_meet=True):
    """Return None if canonical with invariants J, K, A; else a reason string."""
    if any(c == BL for c in cells[1:]) or any(c == BR for c in cells[:-1]): return "blank inside"
    cells = list(cells)
    if state == "A":
        if not (cells[h] == 1 and h + 1 < len(cells) and cells[h + 1] == 1): return "packet shape"
        rest = cells[:h] + cells[h + 2:]; hh = h            # packet removed; the head sits between rest[h-1] and rest[h]
        R = runs(rest)
        gap_run = None
    elif state == "E":
        if cells[h] != 0: return "E not on 0"
        rest = cells; hh = None
        R = runs(rest)
        gap_run = next((r for r in R if r[0] == 0 and r[1] <= h <= r[2]), None)
        if gap_run is None or gap_run[3] or gap_run[4]: return "no gap at head"
        L_ = gap_run[2] - gap_run[1] + 1
        if not ((L_ == 3 and h == gap_run[2]) or (allow_meet and L_ == 4 and h == gap_run[2] - 1)):
            return f"head not at gap end (run {L_})"
    else:
        return "state"
    for (c, i, j, partial, blank) in R:
        n = j - i + 1
        if blank: continue
        if n >= 4 and not (state == "E" and (c, i, j) == gap_run[:3]): return f"run of {n} {c}s"
        if c == 0 and not partial:
            if i == 0 or j == len(rest) - 1: return "0-run at window edge"
        if partial: continue
        # position relative to head
        if state == "E":
            left_of_head = j < gap_run[1]; right_of_head = i > gap_run[2]
        else:                                   # packet phase: runs reaching under the packet count on both sides
            left_of_head = i < hh; right_of_head = j >= hh
        if c == 1 and n == 3 and left_of_head: return "J: block left of head"
        if c == 0 and n == 3 and right_of_head: return "K: gap right of head"
    for a, b in zip(R, R[1:]):
        if a[0] == 0 and b[0] == 1 and a[2] + 1 == b[1] and not a[3] and not b[3] and not a[4]:
            if a[2] - a[1] + 1 == 2 and b[2] - b[1] + 1 == 2: return "A: wall directly before marker"
    # content must start and end with 1 next to blank tape
    if rest and rest[0] == BL and len(rest) > 1 and rest[1] == 0: return "content starts with 0"
    if rest and rest[-1] == BR and len(rest) > 1 and rest[-2] == 0: return "content ends with 0"
    return None

def contexts():
    Ls = [[HL] + list(s) for s in itertools.product([0, 1], repeat=6)]
    Ls += [[BL] + list(s) for n in range(0, 7) for s in itertools.product([0, 1], repeat=n) if not s or s[0] == 1]
    Rs = [list(s) + [HR] for s in itertools.product([0, 1], repeat=6)]
    Rs += [list(s) + [BR] for n in range(0, 7) for s in itertools.product([0, 1], repeat=n) if not s or s[-1] == 1]
    return Ls, Rs

def theorem_steps():
    """(name, start pattern, end pattern, variables) for every macro step."""
    out = []
    for t in proofs.THEOREMS:
        if t["halt"]: continue
        s, e = t["start"], t["end"]
        varnames = sorted(set(s[3]) | set(e[3]))
        out.append((t["name"], s, e))
    out.append(("CARRY(one pair)", ("L 1 0", "A", "1 1 R", {}), ("L", "A", "1 1 1 0 R", {})))
    return out

def run_check(verbose=False):
    Ls, Rs = contexts()
    vals = range(0, 4)
    report = {}
    for name, s, e in theorem_steps():
        bad = {}; tested = 0
        uses_L = "L" in s[0].split() ; uses_R = "R" in s[2].split()
        for m in vals:
            for j in vals:
                v = dict(m=m, j=j, m1=m + 1, m2=m + 2)
                sv = {k: v[k] for k in ("m", "j", "m1", "m2")}
                for cl in (Ls if uses_L else [[]]):
                    for cr in (Rs if uses_R else [[]]):
                        st = window((s[0], s[1], s[2]), cl, cr, {**sv})
                        why = check(*st)
                        if why: continue
                        tested += 1
                        en = window((e[0], e[1], e[2]), cl, cr, {**sv})
                        why2 = check(*en)
                        if why2:
                            key = why2
                            if key not in bad: bad[key] = (m, j, cl, cr, st, en)
        report[name] = (tested, bad)
        print(f"{name:26s} tested {tested:7d}  violations: {list(bad) if bad else 'none'}", flush=True)
        if verbose:
            for k, ex in bad.items():
                print("     example", k, ex[:4])
    return report

if __name__ == "__main__":
    run_check(verbose="-v" in sys.argv)
