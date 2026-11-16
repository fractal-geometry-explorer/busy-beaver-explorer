"""Put the hand-written explainer sections (page/*.html) into status.json; then run holdouts/build_pages.py.

    python3 py/page.py
"""
import json
import os

D = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
SECTIONS = [
    ("levels", "Four levels", "From six states to three numbers"),
    ("visits", "Level 1 to level 2", "The tape at its visits"),
    ("odometer", "Level 2", "Three wheels"),
    ("doublingmap", "Level 3", "Doubling modulo a growing number"),
    ("laps", "Level 4", "Laps, and why they get rarer"),
    ("definition", "The bottom line", "The whole question in one definition"),
]

path = os.path.join(D, "status.json")
spec = json.load(open(path))
spec["explainer"]["sections"] = [
    {"id": i, "eyebrow": e, "heading": h, "html": open(os.path.join(D, "page", i + ".html")).read().rstrip("\n").split("\n")}
    for i, e, h in SECTIONS]
with open(path, "w") as f:
    json.dump(spec, f, indent=1, ensure_ascii=False)
    f.write("\n")
