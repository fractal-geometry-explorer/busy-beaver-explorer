"""Independent TNF parsing and machine transforms for the cross-check (no imports from tools/)."""
STATES = "ABCDEF"

def parse(name):
    rows = name.split("_")
    assert len(rows) == 6, name
    t = {}
    for qi, row in enumerate(rows):
        assert len(row) == 6, name
        for b in (0, 1):
            c = row[3 * b:3 * b + 3]
            if c == "---":
                t[(STATES[qi], b)] = None
            else:
                assert c[0] in "01" and c[1] in "LR" and c[2] in STATES, name
                t[(STATES[qi], b)] = (int(c[0]), c[1], c[2])
    return t

def unparse(t):
    out = []
    for q in STATES:
        row = ""
        for b in (0, 1):
            v = t[(q, b)]
            row += "---" if v is None else f"{v[0]}{v[1]}{v[2]}"
        out.append(row)
    return "_".join(out)

def mirror(name):
    t = parse(name)
    return unparse({k: (None if v is None else (v[0], "L" if v[1] == "R" else "R", v[2])) for k, v in t.items()})
