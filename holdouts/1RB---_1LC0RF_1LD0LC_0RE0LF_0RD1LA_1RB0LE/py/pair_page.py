"""Write the sections on the shared halting question into the explainers of both machines.

usage: python3 py/pair_page.py          (from anywhere; then python3 holdouts/build_pages.py M for both machines)

1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE and 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC halt together or not at
all (lean/Lockstep.lean + lean/RightEnd.lean, and coq/Eqv_TailWord.v). Five hand-written sections explain why, with
the interactive parts in py/pair/pair.js (tested by py/pair/test_pair.js) and their style in py/pair/pair.css. The
same sections go into both status.json files ("explainer.sections", ids pair-*), placed after the section named in
AFTER; running this again replaces them.
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
M1 = "1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE"
M2 = "1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC"
AFTER = {M1: "wall", M2: "counter"}
GH = "https://github.com/fractal-geometry-explorer/busy-beaver-explorer/blob/main/holdouts/" + M1
FORK = "https://github.com/fractal-geometry-explorer/busycoq/blob/claude/project-thread-tinjly/verify/Eqv_TailWord.v"


def read(name):
    with open(os.path.join(HERE, "pair", name)) as f:
        return f.read()


def link(m, here):
    return f"<code>{m}</code>" + (" (this page)" if m == here else f" (<a href=\"../{m}/explainer.html\">its page</a>)")


def sections(here):
    first, second = link(M1, here), link(M2, here)
    s1 = f"""<style>
{read("pair.css")}</style>
<div class="col">
<p>Two of the 608 holdouts are one halting question. Call {first} the <b>first machine</b> and {second} the
<b>second machine</b>. It is proved, in Lean and again in Coq, that the first halts from blank tape if and only if the
second does. That does not say whether either one halts: it says that the list of open machines is one shorter
than it looks. The next five sections show why, and let you check each piece in the browser.</p>
<p>It starts with the tables. Point at (or tap) any cell of one table and the matching cell of the other lights up:
the same symbol is written, the direction is reversed, and the states are renamed A&rarr;D, B&rarr;E, C&rarr;A,
D&rarr;B, E&rarr;C, F&rarr;F. So the second machine is the first one watched in a mirror, with different names on
the states. The one real difference is where it starts: the second machine's A is the first machine's C.</p>
</div>
<div class="panel">
  <div class="tq-tables" id="tqTables"></div>
  <div class="tq-say" id="tqTableSay" aria-live="polite"></div>
  <div class="controls"><button id="tqBack">Translate the second table back</button></div>
  <p class="small" id="tqBackSay" hidden>Renaming the second table's states back and exchanging left and right gives
  the first table exactly, the halting cell included (the green table). The machines differ only in the state they
  start in: C instead of A.</p>
</div>
<div class="col">
<p>A different start state usually means a different run, and the related-machines screen found no common
configuration in the first 10<sup>7</sup> steps. But it compared the runs <em>step for step</em>. The next section
compares them <em>event for event</em>.</p>
</div>"""
    s2 = f"""<div class="col">
<p>Run both machines from blank tape. After 2 steps of the first and 49 of the second, the two tapes are the same
when the second is read in a mirror, except that the second has one more word, <code>10001101</code>, at the far right
end. From then on each step of one is a step of the other, with one exception. When the head moves right from
<b>q</b>, the rightmost cell visited so far, it crosses the end of the tape. The first machine does that in 5
steps; the second has to cross the extra word too and takes 49. Call one step of both, or one crossing, a
<b>model step</b>. Below, the two runs are drawn on the model-step clock, the second one mirrored. The pictures are
the same except for the extra word on the right (blue band), and the head (orange) is always in the same place.</p>
</div>
<div class="panel">
  <div class="controls">
    <label class="small" for="tqLockM">model steps</label>
    <select id="tqLockM"><option value="2000">2,000</option><option value="20000" selected>20,000</option><option value="200000">200,000</option><option value="1000000">1,000,000</option></select>
    <button class="primary" id="tqLockGo">Draw</button>
  </div>
  <div class="tq-two">
    <div><div class="small">first machine, <code>{M1}</code></div><canvas id="tqLock1" aria-label="space-time diagram of the first machine"></canvas></div>
    <div><div class="small">second machine in a mirror, <code>{M2}</code></div><canvas id="tqLock2" aria-label="space-time diagram of the second machine, mirrored"></canvas></div>
  </div>
  <div class="tq-key"><span><i style="background:var(--ink)"></i>1</span><span><i style="background:var(--head)"></i>head</span><span><i style="background:var(--accent)"></i>the extra word <code>10001101</code></span><span>time runs down; one row per model step (sampled)</span></div>
  <p class="tq-say" id="tqLockSay" aria-live="polite"></p>
  <div class="controls">
    <button id="tqLockCheck">Check the runs in lockstep</button>
    <label class="small" for="tqLockN">up to</label>
    <select id="tqLockN"><option value="10000000" selected>10,000,000 steps</option><option value="100000000">100,000,000 steps</option></select>
  </div>
  <p class="small" id="tqLockCheckSay" aria-live="polite">Runs both machines in your browser and compares the whole tapes at every crossing.</p>
</div>
<div class="col">
<p>This is <span class="ev c">Computed</span> evidence for a few million steps; the C program <code>c/lockstep.c</code>
checked 10<sup>11</sup> steps (270,284 visits to the left end). The proof that it lasts for ever has two parts: the
crossing itself (next section) and the fact that the head never leaves q in any other way (the section after).</p>
</div>"""
    s3 = """<div class="col">
<p>Here is the one place where the two runs come apart for a moment, drawn in the first machine's frame (the
second machine's run is this, mirrored). Both lanes start from the same configuration of the real run, just before its
third crossing: state B on the 1 at q (green outline). The lower lane has k extra words after q (blue). The slider
moves both lanes together; the upper one takes 5 steps, the lower one 44k + 5.</p>
</div>
<div class="panel">
  <div class="controls">
    <button class="primary" id="tqFarPlay">Play</button><button id="tqFarStep">Step</button>
    <input type="range" class="tq-range" id="tqFarT" min="0" max="49" value="0" aria-label="time through the crossing">
    <label class="small" for="tqFarK">extra words k = <b id="tqFarKv">1</b></label>
    <input type="range" id="tqFarK" min="0" max="4" value="1" style="width:110px;accent-color:var(--accent)">
  </div>
  <div class="tq-lane"><div class="small" id="tqFarAs"></div><div class="cells" id="tqFarA"></div></div>
  <div class="tq-lane"><div class="small" id="tqFarBs"></div><div class="cells" id="tqFarB"></div></div>
  <p class="tq-say" id="tqFarSay" aria-live="polite"></p>
</div>
<div class="col">
<p>Whatever k is, the head walks right through the words, turns at the blank end and walks back, and both lanes end in
state D one cell left of q with <code>1 0 1</code> written from q on: q has moved two cells right and the extra words
moved with it. Lean proves this for every k (<code>far_B</code>, 44k + 5 steps, in <code>lean/FarEnd.lean</code>);
Coq needs only k = 0 and k = 1 (<code>far0</code>, <code>far1</code>, each checked by running the machine).</p>
</div>"""
    s4 = """<div class="col">
<p>Could the head ever leave q in some other state, or on a 0? Then the first machine would step onto a blank cell
while the second steps onto the extra word, and the runs would part. The proof rules this out by looking only at the
last four cells of the tape, q&minus;3 to q, the <b>window</b>, and forgetting everything to their left. A card below
is one <b>abstract configuration</b>: the four cells, and the state and head position when the head is in the window.
When the head is further left (card <i>out</i>) even the state is forgotten, and the head may come back in any state
that a move to the right can produce: B, D, E or F.</p>
<p>From the start there are exactly <b id="tqWinCount">28</b> of them, and none moves right from q except in state B on
a 1 (green cards: the crossing). Click a card to see where one step can lead (blue): always to another card. That
closure is the whole invariant; Coq checks it with one <code>vm_compute</code> (<code>check_S0</code>).</p>
</div>
<div class="panel">
  <div class="controls"><button class="primary" id="tqWinRun">Follow the real run</button>
    <label class="small" for="tqWinMut">or break the table:</label>
    <select id="tqWinMut" style="max-width:100%"><option value="">flip one direction&hellip;</option></select></div>
  <p class="small" id="tqWinRunSay" aria-live="polite"></p>
  <p class="small" id="tqWinMutSay" aria-live="polite"></p>
  <div class="tq-grid" id="tqWin"></div>
  <p class="tq-say" id="tqWinSay" aria-live="polite"></p>
</div>
<div class="col">
<p>The window works because the left end of the tape cannot reach it unseen. When the head leaves the window to the
left, the window's last three cells always read <code>1 0 1</code> (the two <i>out</i> cards), and whatever the
counter does far to the left, the head can only come back through the window's first cell. The window is a
deliberately coarse picture, an over-approximation: it allows more than the machine does, so if even the coarse
picture never leaves q the wrong way, the real run cannot. The Lean proof uses a slightly finer window with 32
configurations (<code>lean/RightEnd.lean</code>, <code>closed</code> by <code>decide</code>); the Coq proof was written
on its own and lands on 28.</p>
</div>"""
    s5 = f"""<div class="col">
<p>The Coq proof is one file of 371 lines, <a href="{GH}/coq/Eqv_TailWord.v"><code>coq/Eqv_TailWord.v</code></a>,
built on the definitions of <a href="https://github.com/ccz181078/busycoq">busycoq</a>, the Coq library in which the
bbchallenge results are checked. It is meant for busycoq itself, in the style of its <code>Eqv_WordPairs.v</code>. Its
steps, from the machines to the theorem:</p>
</div>
<ol class="tq-ladder">
 <li><b>The mirror</b><span class="small">Every transition of the second table is the first's with the direction
 reversed and the states renamed by <code>g</code>. <code>tm'_some</code>, <code>tm'_none</code>; 12 cases.</span></li>
 <li><b>One model for both runs</b><span class="small">A configuration <code>Cfg</code> keeps the window apart from the
 rest of the tape. <code>to_config false</code> reads it as a configuration of the first machine;
 <code>to_config true</code> as the mirrored configuration of the second, with <code>W8 = 10001101</code> after q.</span></li>
 <li><b>The model step</b><span class="small"><code>f</code> is one step of both machines, or the crossing at the far
 end. <code>far0</code> (5 steps) and <code>far1</code> (49 steps) are run by busycoq's <code>execute</code>.
 <code>f_spec</code>: each model step is at least one step of whichever machine you read it as, and a model halt is a
 halt of both.</span></li>
 <li><b>The invariant</b><span class="small"><code>P c</code>: the window of c is one of the 28 cards of
 <code>S0</code>. <code>check_S0</code> (one <code>vm_compute</code>) shows the list is closed under the abstract step
 and that no card leaves q except B on a 1; <code>anext_spec</code> shows the abstract step covers the real one.</span></li>
 <li><b>The start</b><span class="small"><code>init0</code>, <code>init1</code>: from blank tape the first machine
 reaches the model's start in 2 steps, the second in 49.</span></li>
 <li><b>The theorem</b><span class="small">busycoq's <code>halts_iff</code> turns the model into
 <code>halts (machine b) c0 &lt;-&gt; iter_halts f cfg0</code> for both b, so
 <code>TailWord.eqv : halts tm c0 &lt;-&gt; halts tm' c0</code>.</span></li>
</ol>
<div class="tq-checks">
 <div><b>Coq 8.20.1</b>busycoq's own version. The core up to <code>Individual62.v</code>, then the file: 2.4 s, no
 warnings of its own. Also checked on Coq 8.18.0.</div>
 <div><b>No axioms</b><code>Print Assumptions TailWord.eqv</code>: <i>Closed under the global context</i>.</div>
 <div><b>It can fail</b>Changing the word W8, one transition of the second machine, or removing one card from
 <code>S0</code> each makes the file fail to compile.</div>
 <div><b>Two proofs</b>The Lean proof (<code>two_machines'</code> in <code>lean/Lockstep.lean</code> with
 <code>good30773</code> in <code>lean/RightEnd.lean</code>) came first; the Coq file is an independent second proof,
 with its own invariant.</div>
</div>
<div class="col">
<p><span class="ev k">Kernel</span> The two machines halt together. <span class="ev o">Open</span> Whether they halt.
The Coq file is on a branch of a fork of busycoq (<a href="{FORK}">Eqv_TailWord.v</a>), ready to be proposed
upstream; it has not been submitted or reviewed there yet. If it is merged, bbchallenge can count these two holdouts
as one.</p>
<p>Build it yourself: <code>sh holdouts/{M1}/coq/build.sh /path/to/busycoq</code> with a checkout of busycoq's
<code>BB6</code> branch and Coq 8.20.1 (or 8.18).</p>
</div>
<script>
{read("pair.js")}</script>"""
    return [
        {"id": "pair-tables", "eyebrow": "One question, two machines", "heading": "Two tables that are one machine", "html": s1},
        {"id": "pair-lockstep", "eyebrow": "The two runs", "heading": "One run, watched in a mirror", "html": s2},
        {"id": "pair-farend", "eyebrow": "Where they part", "heading": "Crossing the far end: 5 steps against 49", "html": s3},
        {"id": "pair-window", "eyebrow": "The invariant", "heading": "Four cells that settle it", "html": s4},
        {"id": "pair-proof", "eyebrow": "The proof", "heading": "Checked in Coq, step by step", "html": s5},
    ]


def main():
    for m in (M1, M2):
        p = os.path.join(ROOT, m, "status.json")
        with open(p) as f:
            d = json.load(f)
        secs = [s for s in d["explainer"]["sections"] if not s["id"].startswith("pair-")]
        at = next(i for i, s in enumerate(secs) if s["id"] == AFTER[m]) + 1
        d["explainer"]["sections"] = secs[:at] + sections(m) + secs[at:]
        with open(p, "w") as f:
            json.dump(d, f, indent=1, ensure_ascii=False)
            f.write("\n")
        print("wrote", p)


if __name__ == "__main__":
    main()
