#!/usr/bin/env python3
"""Builds pages/deciders.html by inlining engine.js and data/coq_hardcoded.json into page.html.
Run: python3 pages/src/deciders/build.py   (add --check to verify the built page is current)."""
import json, os, sys

S = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(S, "..", "..", "deciders.html")

def build():
    page = open(os.path.join(S, "page.html"), encoding="utf-8").read()
    engine = open(os.path.join(S, "engine.js"), encoding="utf-8").read()
    data = json.load(open(os.path.join(S, "data", "coq_hardcoded.json"), encoding="utf-8"))
    blob = json.dumps(data, separators=(",", ":")).replace("</", "<\\/")
    if "</script" in engine.lower():
        raise SystemExit("engine.js must not contain </script")
    for k in ("/*DATA*/", "/*ENGINE*/"):
        if page.count(k) != 1:
            raise SystemExit(f"page.html must contain {k} exactly once")
    return page.replace("/*DATA*/", blob).replace("/*ENGINE*/", engine.rstrip())

if __name__ == "__main__":
    html = build()
    if "--check" in sys.argv:
        cur = open(OUT, encoding="utf-8").read() if os.path.exists(OUT) else ""
        if cur != html:
            raise SystemExit("pages/deciders.html is stale: run python3 pages/src/deciders/build.py")
        print("deciders.html is up to date")
    else:
        open(OUT, "w", encoding="utf-8").write(html)
        print(f"wrote {os.path.relpath(OUT)} ({len(html):,} bytes)")
