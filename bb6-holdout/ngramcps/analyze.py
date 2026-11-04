"""Read the derivations written by run.py and say, for each run that reached a halt, how it got there.

usage: python3 analyze.py OUTDIR [OUTDIR ...]  ->  a table on stdout (Markdown), one row per run

Columns: the run (augmentation, widths), the length of the derivation, the halting move (the last five local
configurations; PACKET->block is `0 1 1 A>1 1`, the only halting rule of the mark model: A1 -> E1 -> B0 -> C1 -> D1),
the first local configuration that the direct run from blank tape never shows, and what the window glued in there
did to a stripe `1010...`:
  cut        the known cells of the window on that side are all stripe and the glued cell ends the stripe (two equal
             cells): the decider assumed the stripe stops right there, just beyond what the window could see
  continued  the known cells are all stripe and the glued cell continues it
  other      the known cells hold a mark already (the glued cell then misplaces the next one)
"""
import os, sys


def parse(path):
    rows = []
    for line in open(path):
        if line.startswith("#"):
            continue
        f = line.split()
        step, left, sh, right = int(f[0]), f[1], f[2], f[3]
        real = f[4] if len(f) > 4 and f[4] in ("real", "UNREAL") else None
        glued = None
        if "glued" in f:
            i = f.index("glued")
            glued = (f[i + 1], f[i + 2])
        rows.append(dict(step=step, left=left, state=sh[0], head=sh[1:], right=right, real=real, glued=glued))
    return rows


def alternating(w):
    return all(w[i] != w[i + 1] for i in range(len(w) - 1))


def classify(cur):
    side, g = cur["glued"]
    if side == "L":          # stepped left: the left window lost its near cell and gained a far cell (g[0])
        far = g[0]
        known_cells = g[1:]
    else:
        far = g[-1]
        known_cells = g[:-1]
    if len(known_cells) == 0:
        return "other"
    neighbour = known_cells[0] if side == "L" else known_cells[-1]   # the known cell next to the glued one
    if alternating(known_cells) and len(known_cells) >= 2:
        return "cut" if far == neighbour else "continued"
    return "other"


def halting_move(rows):
    tail = rows[-5:]
    a = tail[0]
    pat = a["state"] == "A" and a["head"] == "1" and a["left"].endswith("011") and a["right"].startswith("1")
    seq = "".join(r["state"] for r in tail)
    if pat and seq == "AEBCD":
        return "PACKET->block"
    if seq.endswith("BCD"):
        return "PACKET->block, window too short to show it (" + seq + ")"
    return "other: " + seq


def main():
    print("| run | widths | derivation | halting move | first unreal step | what the glued window did there |")
    print("|---|---|---|---|---|---|")
    for out in sys.argv[1:]:
        d = os.path.join(out, "deriv")
        names = sorted(os.listdir(d), key=lambda s: (s.split("_")[0], int(s.split("_")[1]), int(s.split("_")[2].split(".")[0])))
        for name in names:
            rows = parse(os.path.join(d, name))
            if not rows:
                continue
            aug, nl, nr = name[:-4].split("_")
            fu = next((i for i, r in enumerate(rows) if r["real"] == "UNREAL"), None)
            what = ""
            if fu is not None and fu > 0 and rows[fu]["glued"]:
                what = classify(rows[fu])
                side, g = rows[fu]["glued"]
                what += f" ({side} {g})" if len(g) <= 40 else f" ({side}, {len(g)} cells)"
            print(f"| {aug} | {nl} {nr} | {len(rows) - 1} | {halting_move(rows)} | {fu} | {what} |")


if __name__ == "__main__":
    main()
