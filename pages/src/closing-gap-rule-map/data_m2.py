"""Collects everything the page needs from one step-by-step run of the machine, so every frame,
sequence and number on the page comes from the simulation."""
import json
from m2sim import TM, classify, tokens

# steps whose full tape we keep (frames, snapshots)
FRAME_RANGES = [(0, 46), (1376, 1412), (2794, 2842), (3903, 3936), (4180, 4702), (43385, 43400), (79540, 79560)]
TRACE_RANGES = {"setup": (0, 46), "example": (4180, 4700), "cycle": (43385, 79549)}

def collect():
    want = set()
    for a, b in FRAME_RANGES:
        want.update(range(a, b + 1))
    end = max(max(b for _, b in TRACE_RANGES.values()), max(b for _, b in FRAME_RANGES)) + 1
    m = TM()
    snaps = {}
    traces = {k: {"pos": [], "key": [], "rule": [], "lo": [], "hi": []} for k in TRACE_RANGES}
    hist = {k: [] for k in TRACE_RANGES}   # per-step list of (pos, written value) for tape history
    while m.steps <= end:
        s = m.steps
        if s in want:
            snaps[s] = {"t": dict(m.t), "pos": m.pos, "st": m.st, "key": m.key(), "rule": m.rule()}
        for k, (a, b) in TRACE_RANGES.items():
            if a <= s <= b:
                tr = traces[k]
                tr["pos"].append(m.pos); tr["key"].append(m.key()); tr["rule"].append(m.rule())
        if not m.step():
            raise SystemExit("halted?")
    return snaps, traces

SNAPS, TRACES = collect()

def frame(step, lo, hi):
    s = SNAPS[step]
    cells = "".join(str(s["t"].get(i, 0)) for i in range(lo, hi + 1))
    head = s["pos"] - lo if lo <= s["pos"] <= hi else None
    return {"step": step, "state": s["st"], "key": s["key"], "rule": s["rule"], "cells": cells, "head": head}

def content(step):
    t = SNAPS[step]["t"]
    ones = [i for i, v in t.items() if v]
    return min(ones), max(ones)

def kinds(name, pad_before=None):
    """Routine kind for every step of a traced range (classification needs some context before)."""
    keys = TRACES[name]["key"]
    k, toks, words = classify(keys)
    return k
