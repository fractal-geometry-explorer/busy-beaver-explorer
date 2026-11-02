"""Write the run data of pages/1RB1RF_1LC0LB/explainer.html (the block `<script type="application/json" id="run-data">`).

usage: python3 bb6-1RB1RF_1LC0LB/py/explainer_data.py       (tests/test_explainer.py checks that the page is current)

The data: the transition counts of the first 10^6 steps (`blank.rare`), the left-end moments of `runs/left_1e10.txt`,
the walls that `replay.walls` finds in them, and the growth table `runs/growth_1e10.txt`.  The status panel of the
same page is written from status.json by tools/pages/explainer_status.py.
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
REPO = os.path.dirname(ROOT)
PAGE = os.path.join(REPO, "pages", "1RB1RF_1LC0LB", "explainer.html")
sys.path.insert(0, HERE)

import blank  # noqa: E402
import replay  # noqa: E402

BLOCK = re.compile(r'(<script type="application/json" id="run-data">\n)(.*?)(\n</script>)', re.S)


def data():
    counts = {f"{s}{y}": c for (s, y), c in sorted(blank.rare(10 ** 6).items())}
    left = []
    with open(os.path.join(ROOT, "runs", "left_1e10.txt")) as f:
        for line in f:
            p = line.split(maxsplit=4)
            left.append([int(p[0]), int(p[2]), p[3], p[4].strip()])
    walls = [{"step": t, "event": j, "wall": w, "replayed": n, "after": rest}
             for t, j, w, n, rest in replay.walls(replay.read_events(os.path.join(ROOT, "runs", "left_1e10.txt")))
             if n >= 2]
    growth = []
    with open(os.path.join(ROOT, "runs", "growth_1e10.txt")) as f:
        for line in f:
            growth.append([int(x) for x in line.split()])
    return {"counts": counts, "left": left, "walls": walls, "growth": growth}


def payload(d):
    return json.dumps(d, separators=(",", ":")).replace("</", "<\\/")


def build(page, d):
    m = BLOCK.search(page)
    if not m:
        raise ValueError("no run-data block in the page")
    return page[:m.start(2)] + payload(d) + page[m.end(2):]


def main():
    with open(PAGE) as f:
        page = f.read()
    out = build(page, data())
    if out != page:
        with open(PAGE, "w") as f:
            f.write(out)
    print("wrote" if out != page else "unchanged", PAGE)


if __name__ == "__main__":
    main()
