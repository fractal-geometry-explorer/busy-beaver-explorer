"""Put the hand-written explainer sections (page/*.html) into status.json; then run holdouts/build_pages.py.

    python3 py/page.py
"""
import json
import os

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
SECTIONS = [
    ("levels", "Four levels", "From six states to a ladder of numbers"),
    ("shape", "First look", "The shape of the run"),
    ("words", "Reading the tape", "Pairs, digits, and a front"),
    ("digit", "Level 1 to level 2", "Every level is a digit with 16 positions"),
    ("transparent", "Level 2 to level 3", "Levels are transparent"),
    ("fuel", "Level 3 to level 4", "Resets, fuel, and 887 levels"),
    ("halt", "The end", "Off the edge"),
    ("bottomline", "The bottom line", "It halts, at a step with 759 digits"),
    ("trust", "How sure is this?", "What the result rests on"),
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
