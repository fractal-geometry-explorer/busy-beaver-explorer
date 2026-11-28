"""Split a long symbolic-run theorem (as `symtm.prove` writes it) into segment theorems, so that Lean elaborates
it in pieces: each segment proves a run of consecutive steps, and the theorem chains the segments.  Used by
py/copyloop.py for runs that would otherwise take Lean out of memory."""
import re


def _paren_end(s, i):
    d = 0
    for k in range(i, len(s)):
        if s[k] == "(":
            d += 1
        elif s[k] == ")":
            d -= 1
            if d == 0:
                return k + 1
    raise ValueError("unbalanced")


def _parse_type(t):
    """steps N ⟨A⟩ = some ⟨B⟩  ->  (N, ⟨A⟩, ⟨B⟩)"""
    assert t.startswith("steps "), t[:40]
    r = t[6:]
    if r.startswith("("):
        k = _paren_end(r, 0)
        n, rest = r[:k], r[k:].lstrip()
    else:
        n, rest = r.split(" ", 1)
    a, b = rest.split(" = some ", 1)
    return n, a, b


def split_theorem(text, seg=40, pieces=False):
    """the segment theorems and the theorem that chains them, as one text (pieces: as a list of texts, the
    chaining theorem last)"""
    lines = text.rstrip("\n").split("\n")
    doc = []
    while not lines[0].startswith("theorem "):
        doc.append(lines.pop(0))
    head = []
    while not lines[0].startswith("  have hn"):
        head.append(lines.pop(0))
    header = "\n".join(head)
    m = re.match(r"theorem (\S+)(.*?) :\n", header + "\n", re.S)
    name, binders = m.group(1), m.group(2)
    args = []
    for grp in re.findall(r"\(([^():]*):", binders):
        args += grp.split()
    hn = lines.pop(0)
    closed = hn[:hn.rindex(" := by omega")].rsplit(" = ", 1)[1]
    exact = lines.pop()
    assert exact.startswith("  exact steps_congr trans hn"), exact[:60]
    # the haves, each with its continuation lines
    items = []
    for ln in lines:
        if ln.startswith("  have "):
            items.append([ln])
        else:
            items[-1].append(ln)
    hs = []           # (index, [c item lines], [h item lines], n, A, B)
    pend = []
    for it in items:
        nm = it[0].split()[1]
        if nm.startswith("c"):
            pend.append(it)
            continue
        t = it[0][len(f"  have {nm} : "):]
        t = t[:t.rindex(" :=")] if " :=" in t else t
        n, a, b = _parse_type(t)
        hs.append((nm, pend, it, n, a, b))
        pend = []
    segs = [hs[i:i + seg] for i in range(0, len(hs), seg)]
    out = []
    sums = []
    for si, sg in enumerate(segs):
        total = sg[-1][3]
        for h in reversed(sg[:-1]):
            total = f"{h[3]} + ({total})"
        sums.append(total)
        chain = sg[-1][0]
        for h in reversed(sg[:-1]):
            chain = f"steps_seq trans {h[0]} ({chain})"
        body = "\n".join("\n".join(c) for h in sg for c in h[1] + [h[2]])
        out.append(f"/-- Steps {sg[0][0][1:]} to {sg[-1][0][1:]} of `{name}`. -/\n"
                   f"theorem {name}_s{si}{binders} :\n    steps ({total}) {sg[0][4]} = some {sg[-1][5]} := by\n"
                   f"{body}\n  exact {chain}\n")
    tot = f"({sums[-1]})"
    for s in reversed(sums[:-1]):
        tot = f"({s}) + ({tot})"
    chain = f"{name}_s{len(segs) - 1} {' '.join(args)}"
    for si in reversed(range(len(segs) - 1)):
        chain = f"steps_seq trans ({name}_s{si} {' '.join(args)}) ({chain})"
    out.append("\n".join(doc) + ("\n" if doc else "") + header + "\n"
               f"  have hn : {tot} = {closed} := by omega\n  exact steps_congr trans hn ({chain})\n")
    return out if pieces else "\n".join(out)
