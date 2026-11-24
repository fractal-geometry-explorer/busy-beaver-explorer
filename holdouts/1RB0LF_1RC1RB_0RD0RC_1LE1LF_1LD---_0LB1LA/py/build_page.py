"""Puts the phase map into status.json (claims, headline cards, the explainer's phase section and its viewer), from
results/summary.json and the viewer data of py/page_data.py, then rebuilds both pages (holdouts/build_pages.py).
usage: python3 py/build_page.py VIEWER_DATA.json"""
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
D = os.path.join(HERE, "..")
ROOT = os.path.join(D, "../..")
M = "1RB0LF_1RC1RB_0RD0RC_1LE1LF_1LD---_0LB1LA"


def main():
    st = json.load(open(os.path.join(D, "status.json")))
    sm = json.load(open(os.path.join(D, "results/summary.json")))
    pdata = open(sys.argv[1]).read().strip()
    viewer = open(os.path.join(HERE, "viewer.html")).read().replace("__PDATA__", pdata)
    N, T = sm["phases"], sm["log10_t"]
    ev = ", ".join(str(e) for e in sm["events"] if e > 6)
    steps = f"10<sup>{T}</sup>"
    st["asof"] = "Status as of 24 November 2026."
    st["verdict"] = [
        f"<b>The question is open.</b> Lean proves the sweeps' shift rules, the head's whole trip through the long "
        f"block for every length, and the only halting shape (<code>1 D&gt; 0</code>). The phase map, run exactly "
        f"(steps included) to phase {N}, about {steps} steps, never produced it; the law of the phases is observed, "
        f"not proved."]
    claims = [c for c in st["claims"] if c["title"] not in ("Sweeps and phases", "Does it halt from blank tape?")
              and not c["title"].startswith("The trip through the block")
              and not c["title"].startswith("No halt to phase")
              and not c["title"].startswith("The law of the phases")]
    claims.append({
        "level": "kernel", "title": "The trip through the block, for every length",
        "text": "Leaving the counter as <code>0 0 D&gt;</code> (or <code>1 0 C&gt; 0</code>) with <code>(10)^(k+1) "
                "(11)^(2j+2)</code> and blank tape to its right, the head crosses the block, turns and comes back, "
                "F (or A) on the block's first cell, in 8j + 12k + 32 (or + 34) steps, with 4 more ones and the "
                "counter unread. With an odd number of ones the same trip halts at the far end. So a sweep depends "
                "only on the counter (and K mod 4), and the right end never halts.",
        "where": "<code>pass_d</code>, <code>pass_c</code>, <code>pass_d_halt</code>, <code>pass_c_halt</code>, "
                 "<code>lean/Passes.lean</code>"})
    claims.append({
        "level": "trusted", "title": f"No halt to phase {N}, about {steps} steps (phase map)",
        "text": f"<code>py/phasemap.py</code> runs the machine exactly, step count included: each sweep on the "
                f"counter with the block cut to 32 + K mod 4 cells and lifted (the trip above), runs of sweeps that "
                f"stay in a suffix of the counter cached as an odometer would be, and phase changes run in full "
                f"(checked linear in Z). It reached the start of phase {N}, step {sm['t_text']}, with no halt. "
                f"Check: the starts of phases 1 to 13 (to step 2,411,853,311) agree, tape and step, with the same "
                f"sweeps run on the whole tape without the cut or the cache; block cuts of 32, 40 and 48 give the "
                f"same first 60 phases. A bounded run: it says nothing about later phases.",
        "where": f"<code>py/phasemap.py</code>, <code>c/sweep.c</code>, <code>results/phases.tsv</code>"})
    claims.append({
        "level": "heuristic", "title": f"The law of the phases (phases 1 to {N})",
        "text": f"Phase n starts with <code>w 1^K 0^1</code> (phase 1 at step 13 with K = 6). Then K<sub>n+1</sub> = "
                f"2K<sub>n</sub> + c<sub>n</sub> with c = 2 except at phases 3 to 6 and {ev} (c = 10), so from phase "
                f"11 on K<sub>n</sub> + 2 = 13448&middot;2<sup>n&minus;11</sup> + 8&Sigma;2<sup>n&minus;m</sup> over "
                f"those m &le; n; t<sub>n</sub>/K<sub>n</sub><sup>2</sup> &rarr; 5/6. An event follows exactly the "
                f"phases whose counter ends in <code>1^2 0^2</code>; the counter's last block <code>1^b 0^3</code> "
                f"loses one 1 a phase, so events are about a block length apart.",
        "where": f"<code>results/phases.tsv</code>; README, <i>The phase map</i>"})
    claims.append({
        "level": "open", "title": "Does it halt from blank tape?",
        "text": "Not known. A halt needs <code>1 D&gt; 0</code> inside the counter. Deciding it needs the counter "
                "word as numbers: the odometer of a phase and the list of blocks across phases.", "where": ""})
    st["claims"] = claims
    ex = st["explainer"]
    ex["lede"] = (f"Nobody knows. Started on a blank tape, this Turing machine has been run exactly to about "
                  f"{steps} steps, phase after phase, without stopping. This page runs the real machine in your "
                  f"browser, shows how its phases follow one another, and lists what is known, each result marked "
                  f"by what it rests on.")
    ex["facts"] = [
        {"level": "trusted", "value": steps + " steps", "text": f"No halt: the exact phase map, run to phase {N}."},
        {"level": "native", "value": "10<sup>7</sup> steps", "text": "No halt, proved in Lean; the first 10,000 by "
                                                                    "the kernel alone."},
        {"level": "heuristic", "value": "K' = 2K + 2", "text": "The block doubles each phase, plus 8 at rare events; "
                                                              "each phase about 4 times longer."}]
    secs = [s for s in ex["sections"] if s["id"] not in ("phases", "phasemap")]
    i = next(k for k, s in enumerate(secs) if s["id"] == "sweep") + 1
    secs.insert(i, {"id": "phasemap", "eyebrow": "Many sweeps", "heading": "The phase map", "html": [
        "<p>Sample the tape once a sweep, with C on the 0 at its right end: it reads <code>w 1^K 0^Z</code>, a "
        "counter word <code>w</code>, the long block of K ones, and the Z zeros the block has given back.</p>",
        "<p><b>One sweep depends only on the counter.</b> Lean proves the head's whole trip from the counter across "
        "the block and back, for every K and Z (<code>pass_d</code>, <code>pass_c</code>): the counter is not read, "
        "the block keeps its shape, Z grows by 4 and the step count is linear. The same trip with an odd number of "
        "ones would end in a halt, but the count only ever grows by 4. So a sweep can be run on a short block and "
        "lifted, and the right end of the tape never halts.</p>",
        "<p><b>Many sweeps are an odometer.</b> Inside a phase the counter works like an odometer whose digits are "
        "short runs of ones and zeros: each sweep changes its right end, down to the deepest carry, and takes 1 or 3 "
        "cells from the block (4 every two sweeps). A run of sweeps that stays inside the last v cells depends on "
        "those cells alone, so it is cached and reused, and long runs are built from short ones. Some thousands of sweeps "
        "are run for real per phase, however long the phase.</p>",
        "<p><b>A phase.</b> When the block is used up, the zeros (about 2K of them) become the new block and a phase "
        f"starts with <code>w 1^K 0^1</code>. Phase 1 starts at step 13 with K = 6, then K = 14, 38, 94, 198, 418, "
        f"838, 1678, &hellip; In every phase so far</p>",
        "<pre class=\"config\">K(n+1) = 2 K(n) + 2      except at events, where it is 2 K(n) + 10\n"
        "K(n) + 2 = 13448 &middot; 2^(n-11) + 8 &middot; &Sigma; 2^(n-m)   (n &ge; 11, sum over the events m &le; n)\n"
        "t(n) / K(n)^2 &rarr; 5/6       (a phase lasts about 5K^2/2 steps)</pre>",
        f"<p>The events after phase 6 are phases {ev}. An event follows exactly the phases whose counter ends in "
        "<code>1^2 0^2</code>. Read from its right end the counter is a list of blocks <code>1^b 0^3</code> that "
        "change slowly, and the last block loses one 1 every phase: when it is gone, an event follows, the block "
        "before it becomes the last and merges with its neighbours, and the next event is about that many phases "
        "away. Read off phase 218 (last block 269 cells), this predicted an event at phase 490, and the run found it "
        "there; after it the last blocks merged into one of 2,581 cells, so the next is not due before about phase "
        f"3,080. The exact run reached phase {N} (step {sm['t_text']}) without a halt.</p>",
        viewer]})
    ex["sections"] = secs
    st["check"] = [c for c in st["check"] if "phasemap" not in c] + [
        f"python3 holdouts/{M}/py/phasemap.py --check",
        f"python3 holdouts/{M}/py/phasemap.py 300"]
    st["summary"] = ("A bouncer that rewrites the long block on every sweep while a counter on the left ticks like an "
                     "odometer; when the block is used up the zeros become the next block, so K doubles each phase "
                     "(K' = 2K + 2, plus 8 at rare events) and each phase lasts about 4 times longer.")
    json.dump(st, open(os.path.join(D, "status.json"), "w"), ensure_ascii=False, indent=1)
    open(os.path.join(D, "status.json"), "a").write("\n")
    subprocess.run([sys.executable, os.path.join(ROOT, "holdouts/build_pages.py"), M], check=True, cwd=ROOT)

if __name__ == "__main__":
    main()
