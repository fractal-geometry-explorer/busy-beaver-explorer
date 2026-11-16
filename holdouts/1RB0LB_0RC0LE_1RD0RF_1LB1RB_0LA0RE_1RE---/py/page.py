"""Put the hand-written explainer sections (page/*.html) into status.json; then run holdouts/build_pages.py.

    python3 py/page.py

The sections page/levels.html to page/shape.html are written by hand (page/levels.html also holds the script shared
by the panels, window.YV, with this machine's visit rules); the section "Related machines" is written by
holdouts/related.py and is kept as it is.
"""
import json
import os

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
SECTIONS = [
    ("levels", "Five levels", "From six states to one computation"),
    ("visits", "Level 1 to level 2", "Rounds and visits"),
    ("rewriting", "Level 2 to level 3", "The same rules without the machine"),
    ("counting", "Level 3 to level 4", "Counting visits instead of making them"),
    ("checker", "Level 4 to level 5", "161,210 rounds, then the trap"),
    ("bottomline", "The bottom line", "It halts"),
    ("counters", "Before the proof", "Two counters and an engine"),
    ("shape", "First look", "The shape of the run"),
]
KEEP = ("related-machines",)

path = os.path.join(D, "status.json")
spec = json.load(open(path))
kept = [s for s in spec["explainer"]["sections"] if s["id"] in KEEP]
spec["explainer"]["sections"] = [
    {"id": i, "eyebrow": e, "heading": h, "html": open(os.path.join(D, "page", i + ".html")).read().rstrip("\n").split("\n")}
    for i, e, h in SECTIONS] + kept
with open(path, "w") as f:
    json.dump(spec, f, indent=1, ensure_ascii=False)
    f.write("\n")
