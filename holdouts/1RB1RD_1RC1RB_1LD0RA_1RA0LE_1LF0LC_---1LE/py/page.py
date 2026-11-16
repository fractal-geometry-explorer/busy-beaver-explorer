"""Put the hand-written explainer sections (page/*.html) into status.json; then run holdouts/build_pages.py.

    python3 py/page.py

The section "related-machines" is written by holdouts/related.py and kept as it is, last.
"""
import json
import os

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
SECTIONS = [
    ("levels", "Four levels", "From six states to an odometer of fuel tanks"),
    ("rounds", "Level 1 to level 2", "The compressed tape"),
    ("odometer", "Level 2 to level 3", "One visit is a binary increment"),
    ("jump", "Level 3 to level 4", "Many visits at once: the tanks"),
    ("edge", "The irregular part", "Tanks that run dry, and overflows"),
    ("end", "How it ends", "The carry falls off the tape"),
    ("bottomline", "The bottom line", "It halts, at a step with 132 digits"),
    ("trust", "How sure is this", "Proved in Coq and in Lean, step count included"),
]

path = os.path.join(D, "status.json")
spec = json.load(open(path))
keep = [s for s in spec["explainer"]["sections"] if s["id"] == "related-machines"]
spec["explainer"]["sections"] = [
    {"id": i, "eyebrow": e, "heading": h, "html": open(os.path.join(D, "page", i + ".html")).read().rstrip("\n").split("\n")}
    for i, e, h in SECTIONS] + keep
with open(path, "w") as f:
    json.dump(spec, f, indent=1, ensure_ascii=False)
    f.write("\n")
