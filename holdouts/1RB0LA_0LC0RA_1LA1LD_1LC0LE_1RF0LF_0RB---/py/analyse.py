"""Pictures and measurements for 1RB0LA_0LC0RA_1LA1LD_1LC0LE_1RF0LF_0RB--- (see README.md).

usage: python3 holdouts/1RB0LA_0LC0RA_1LA1LD_1LC0LE_1RF0LF_0RB---/py/analyse.py [image|records|excursions]
  image    pages/holdouts/1RB0LA_0LC0RA_1LA1LD_1LC0LE_1RF0LF_0RB---/defects.png: one row per 2 visit(s) of the head, in state E, to the
           L end of the tape; dark where the tape differs from itself 4 cells further on (the background has period
           4); at most 1500 rows or 4*10^8 steps.
  excursions  how far the head goes from the L end (state E) between consecutive visits, for the visits
           between 2*10^8 and 2.02*10^8 steps: the lengths show at which defect it turns back.
  records  the times the tape grows on its slow side (R), clustered into events, up to 3*10^9 steps (several
           minutes).
"""
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "..", "..", "1RB0LB_1RC0LA_1RD---_0RE1LD_1LF0RF_1LA1RB", "py"))
import sweeps  # noqa: E402

M = "1RB0LA_0LC0RA_1LA1LD_1LC0LE_1RF0LF_0RB---"
PAGES = os.path.join(HERE, "..", "..", "..", "pages", "holdouts", M)

if __name__ == "__main__":
    what = sys.argv[1] if len(sys.argv) > 1 else "image"
    if what == "image":
        os.makedirs(PAGES, exist_ok=True)
        print(sweeps.defect_image(M, 4e8, "E", "L", 2, 4, os.path.join(PAGES, "defects.png")))
    elif what == "excursions":
        for k, n in sweeps.excursions(M, 2.02e8, "E", "L", 2e8):
            print(k, n)
    else:
        for k, w in sweeps.record_clusters(M, 3e9, "R"):
            print(k, w)
