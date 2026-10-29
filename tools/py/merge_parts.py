"""Merge the outputs of a search split into parts (the protocol of tools/c/parts.h).

usage: python3 merge_parts.py PART_FILE... [--allow-missing]

Checks that every part 0..N-1 of one split is present exactly once and finished (its `done P N` line), then writes
the merged lines in the same protocol: `sum` added, `max`/`min` taken with the witness of the lowest-numbered part
that has the extreme value, every `event` kept (sorted by part), and `done all N`.  Merged files can be merged again
with each other only as whole splits (they carry `done all N`), so this refuses them.  Exit status 1 on any problem.
"""
import re
import sys

LINE = re.compile(r"^(sum|max|min) (\S+) (-?\d+)(?: (.*))?$")


def read_part(path):
    sums, maxs, mins, events, done = {}, {}, {}, [], None
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            m = LINE.match(line)
            if m:
                kind, name, v, w = m.group(1), m.group(2), int(m.group(3)), m.group(4) or ""
                if kind == "sum":
                    sums[name] = sums.get(name, 0) + v
                elif kind == "max":
                    if name not in maxs or v > maxs[name][0]:
                        maxs[name] = (v, w)
                else:
                    if name not in mins or v < mins[name][0]:
                        mins[name] = (v, w)
            elif line.startswith("event "):
                events.append(line[6:])
            elif line.startswith("done "):
                parts = line.split()
                if len(parts) != 3 or not parts[1].isdigit() or not parts[2].isdigit():
                    raise ValueError(f"{path}: bad done line {line!r}")
                done = (int(parts[1]), int(parts[2]))
    return dict(sums=sums, maxs=maxs, mins=mins, events=events, done=done)


def merge(paths, allow_missing=False):
    parts, problems = {}, []
    for p in paths:
        r = read_part(p)
        if r["done"] is None:
            problems.append(f"{p}: no done line (the part did not finish)")
            continue
        k, n = r["done"]
        if k in parts:
            problems.append(f"{p}: part {k} appears twice")
            continue
        r["path"] = p
        parts[k] = r
    ns = {r["done"][1] for r in parts.values()}
    if len(ns) > 1:
        problems.append(f"parts of different splits: NPARTS {sorted(ns)}")
    n = max(ns) if ns else 0
    missing = [k for k in range(n) if k not in parts]
    if missing and not allow_missing:
        problems.append(f"missing parts: {missing[:20]}{' ...' if len(missing) > 20 else ''} ({len(missing)} of {n})")
    out = []
    sums, maxs, mins = {}, {}, {}
    for k in sorted(parts):
        r = parts[k]
        for name, v in r["sums"].items():
            sums[name] = sums.get(name, 0) + v
        for name, (v, w) in r["maxs"].items():
            if name not in maxs or v > maxs[name][0]:
                maxs[name] = (v, w)
        for name, (v, w) in r["mins"].items():
            if name not in mins or v < mins[name][0]:
                mins[name] = (v, w)
    for name in sorted(sums):
        out.append(f"sum {name} {sums[name]}")
    for name in sorted(maxs):
        out.append(f"max {name} {maxs[name][0]}" + (f" {maxs[name][1]}" if maxs[name][1] else ""))
    for name in sorted(mins):
        out.append(f"min {name} {mins[name][0]}" + (f" {mins[name][1]}" if mins[name][1] else ""))
    for k in sorted(parts):
        out.extend(f"event {e}" for e in parts[k]["events"])
    if missing:
        out.append(f"# missing parts: {len(missing)} of {n}")
    else:
        out.append(f"done all {n}")
    return out, problems


def main(argv):
    allow = "--allow-missing" in argv
    paths = [a for a in argv if a != "--allow-missing"]
    if not paths:
        print(__doc__, file=sys.stderr)
        return 1
    out, problems = merge(paths, allow)
    for line in out:
        print(line)
    for p in problems:
        print(f"PROBLEM: {p}", file=sys.stderr)
    return 1 if problems else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
