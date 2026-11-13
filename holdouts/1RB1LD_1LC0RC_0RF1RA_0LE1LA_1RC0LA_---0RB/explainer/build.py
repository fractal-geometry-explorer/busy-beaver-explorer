"""Write the explainer sections, verdict and claims of the two quarter-split machines into their status.json.

The two machines (1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB and 1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB) have the
same event map up to the anchor state (D / C) and the gap a split needs (two / three 0s), so one script writes both.
The interactive parts are core.js (the event map, transcribed from lean/Events.lean), spec.js (the examples of the
rule viewer) and widget.js; test.js checks them against the real machines.

usage: python3 holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer/build.py
       python3 holdouts/build_pages.py <machine>     (for each of the two)
"""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
HOLD = os.path.join(HERE, "..", "..")

MACHINES = [
    dict(m="1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB", var="QS_D", A="D", gap=2, gapw="two", first=14,
         kern="10<sup>130</sup>", kern_ev="30,000", nat="10<sup>13179</sup>", nat_ev="2,999,957", checked="457",
         twin="1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB",
         folds="33, 81, 150, 366, 639, 963, 2229, 3357, 5697, 22527",
         halt1="1<sup>5</sup> 0 <b>D&gt;</b> 0", halt1n=3, halt2="1<sup>5</sup> 0 <b>D&gt;</b> 0 1<sup>3</sup> 0 1", halt2n=9,
         cycle="At event 29 the tape is <code>1 D&gt; 0 1<sup>33</sup></code>. Two events later it is <code>1<sup>32</sup> D&gt; 0 1<sup>6</sup></code>, and the split cuts 32 into 8 (left) and 24 (right, making 30). The 30 then moves back to the left of the head piece by piece, the 8 is split into 2 and 6, the pieces are glued together by odd rounds, and two folds later (event 61) the tape is <code>1 D&gt; 0 1<sup>81</sup></code>."),
    dict(m="1RB1LC_1LC0RD_0LE1LA_0RF1RA_1LA0LA_---0RB", var="QS_C", A="C", gap=3, gapw="three", first=10,
         kern="10<sup>137</sup>", kern_ev="29,996", nat="10<sup>13275</sup>", nat_ev="2,999,995", checked="467",
         twin="1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB",
         folds="36, 102, 192, 549, 1113, 5592, 60876, 106005, 343155, 591204",
         halt1="1<sup>5</sup> 0 0 <b>C&gt;</b> 0", halt1n=5, halt2="1<sup>5</sup> 0 0 <b>C&gt;</b> 0 1<sup>3</sup> 0 1", halt2n=11,
         cycle="At event 27 the tape is <code>1 C&gt; 0 1<sup>36</sup></code>. Four events later it is <code>1<sup>34</sup> C&gt; 0 1<sup>9</sup></code>, and the split cuts 34 into 8 (left), 24 (right, making 33) and a remainder of 2. The pieces are glued together again by odd rounds, 36 is split into 9 and 27, and after more splits, shifts and three folds (event 65) the tape is <code>1 C&gt; 0 1<sup>102</sup></code>."),
]


def read(name):
    with open(os.path.join(HERE, name)) as f:
        return f.read()


def bar(parts):
    """A small static picture of a tape: parts are (kind, label) with kind in l, m, c, r, gap, head."""
    col = {"l": "var(--muted)", "m": "var(--accent)", "c": "var(--kernel)", "r": "var(--muted)"}
    out = ['<div style="display:flex;align-items:flex-end;gap:0;margin:26px 0 6px;font:12px var(--mono)">']
    for kind, label, w in parts:
        if kind == "head":
            out.append('<div style="flex:0 0 3px;height:34px;background:var(--head);position:relative"><span style="position:absolute;top:-18px;left:-4px;color:var(--head);font-weight:600">%s</span></div>' % label)
        elif kind == "gap":
            out.append('<div style="flex:0 0 %dpx;text-align:center;color:var(--muted)">%s</div>' % (w, label))
        else:
            out.append('<div style="flex:%d 1 0;height:26px;background:%s;border-radius:3px;color:var(--bg);text-align:center;line-height:26px;overflow:hidden;white-space:nowrap">%s</div>' % (w, col[kind], label))
    out.append("</div>")
    return "".join(out)


def sections(d):
    A, gapw, P = d["A"], d["gapw"], "qs-"
    zeros = " ".join(["0"] * d["gap"])
    s = []
    # 1. the idea
    rows = [
        ("split", "m is even, at least 4, and has %s or more 0s on its left" % gapw,
         "A quarter of the block, &lfloor;m/4&rfloor;, goes to the far side of the gap. Three quarters go to the right block. The remainder, 0 or 2, stays."),
        ("odd", "m is odd, at least 3, and there is more tape further left",
         "The block loses 2, the 0 on its left turns into a 1 (so the gap shrinks by one, and the block joins its neighbour when the gap closes), and the right block gains 3."),
        ("fold", "m is odd, at least 3, and nothing is further left",
         "The odd round repeats by itself until one 1 is left: every 2 ones become 3 on the right. The right block gains 3(m&minus;1)/2. <b>This is the only place where the tape grows by a fixed fraction.</b>"),
        ("shift", "m is even and has %s on its left" % ("a single 0" if d["gap"] == 2 else "one or two 0s"),
         "The block is too close to its neighbour to be split. The head steps over it, and the block (minus one) is now on the right."),
        ("zero, one, two", "m is 0, 1 or 2: what a split leaves behind",
         "The few remaining 1s are handed across the gap. In most of these cases the head then runs to the right behind a marker <code>0 1</code>, the <em>carrier</em>, which passes whole blocks and turns into three 1s at the first pair of 0s or at the end of the tape. A new block of 3 starts there."),
    ]
    table = ('<table style="border-collapse:collapse;width:100%;font-size:.95em"><thead><tr><th style="text-align:left;padding:6px 10px 6px 0;border-bottom:1px solid var(--line-strong)">event</th><th style="text-align:left;padding:6px 10px;border-bottom:1px solid var(--line-strong)">when</th><th style="text-align:left;padding:6px 0 6px 10px;border-bottom:1px solid var(--line-strong)">what happens</th></tr></thead><tbody>'
             + "".join('<tr><td style="vertical-align:top;padding:8px 10px 8px 0;border-bottom:1px solid var(--line);font-family:var(--mono)">%s</td><td style="vertical-align:top;padding:8px 10px;border-bottom:1px solid var(--line)">%s</td><td style="vertical-align:top;padding:8px 0 8px 10px;border-bottom:1px solid var(--line)">%s</td></tr>' % r for r in rows)
             + "</tbody></table>")
    s.append(dict(id="events-idea", eyebrow="The idea", heading="A few blocks of 1s, and five things that can happen to them", html=[
        '<div class="col"><p>After its first few steps this machine keeps its tape very tidy: a handful of solid blocks of 1s, with one to four 0s between them. Some blocks are enormous, and the machine spends almost all of its time sweeping across them. But at certain moments the head comes to rest in the same position: in state %s, on a single 0, with a block of 1s on each side. Call such a moment an <b>anchor</b>.</p></div>' % A,
        bar([("l", "older blocks", 3), ("gap", zeros, 14 * d["gap"]), ("m", "m ones", 4), ("head", A, 0), ("gap", "0", 14), ("c", "c ones", 5), ("gap", "0 0", 28), ("r", "more", 2)]),
        '<div class="col"><p>Write m for the number of 1s just left of the head (blue) and c for the number just right of it (green). What the machine does between one anchor and the next depends only on m, on how many 0s lie to the left of that block, and on whether anything lies further left. There are five cases, and each one is simple arithmetic on the block lengths:</p></div>',
        table,
        '<div class="col"><p>None of this is a guess. Each rule is a theorem checked by Lean for every block length and every surrounding tape, and together they give an exact, fast model of the machine: instead of simulating billions of single steps, apply one rule per anchor. The next two sections let you try that.</p></div>',
    ]))
    # 2. rule viewer
    s.append(dict(id="events-rule", eyebrow="Try it", heading="Watch one rule on the real machine", html=[
        '<div class="col"><p>Pick a rule and block sizes. The page predicts the next anchor with the rule, then runs the actual Turing machine cell by cell and checks that it gets there.</p></div>',
        '<div style="display:flex;flex-wrap:wrap;gap:8px 18px;align-items:center;margin:10px 0">'
        '<label style="display:flex;gap:6px;align-items:center;max-width:100%;min-width:0">rule <select id="qs-rule" style="font:inherit;padding:4px 6px;min-width:0;flex:1 1 auto"></select></label>'
        '<label id="qs-prow"><span id="qs-plab">m</span> = <b id="qs-pval"></b> <input id="qs-p" type="range" style="vertical-align:middle"></label>'
        '<label>right block c = <b id="qs-cval"></b> <input id="qs-c" type="range" style="vertical-align:middle"></label></div>',
        '<p id="qs-rwords" style="margin:6px 0"></p>',
        '<table style="font-family:var(--mono);font-size:.95em;border-collapse:collapse;margin:6px 0"><tr><td style="padding:2px 12px 2px 0;color:var(--muted)">before</td><td id="qs-before"></td></tr><tr><td style="padding:2px 12px 2px 0;color:var(--muted)">after</td><td id="qs-after"></td></tr></table>',
        '<p id="qs-rmsg" style="margin:6px 0"></p>',
        '<div style="overflow-x:auto;max-height:520px;overflow-y:auto;border:1px solid var(--line);border-radius:6px;padding:6px"><canvas id="qs-canvas" role="img" aria-label="space-time diagram of the machine running the chosen rule"></canvas></div>',
    ]))
    # 3. stepper
    btn = 'style="font:inherit;padding:4px 12px"'
    s.append(dict(id="events-run", eyebrow="The run", heading="Follow the run from blank tape, one event at a time", html=[
        '<div class="col"><p>This is the whole run of the machine, replayed with the rules. The strip shows the tape to scale: each bar is a block of 1s, the blue one is m, the green one is c, and the orange line is the head. Below it the same tape is written out with exact lengths, and the text says which rule fired and what it did.</p></div>',
        '<div style="display:flex;flex-wrap:wrap;gap:8px;margin:10px 0">'
        '<button type="button" id="qs-next" %s><b>Next event</b></button><button type="button" id="qs-play" %s>Play</button>'
        '<button type="button" id="qs-n10" %s>+10</button><button type="button" id="qs-fold" %s>To the next fold</button>'
        '<button type="button" id="qs-n1000" %s>+1,000</button><button type="button" id="qs-n30000" %s>+30,000</button>'
        '<button type="button" id="qs-reset" %s>Start over</button></div>' % ((btn,) * 7),
        '<p id="qs-count" style="margin:6px 0"></p>',
        '<div id="qs-strip" style="display:flex;align-items:stretch;height:30px;margin:24px 0 8px"></div>',
        '<p id="qs-tape" style="font-family:var(--mono);font-size:.92em;overflow-wrap:anywhere;margin:6px 0"></p>',
        '<p id="qs-what" style="margin:10px 0;padding:10px 12px;border-left:3px solid var(--accent);background:var(--accent-soft);min-height:3.2em"></p>',
        '<div class="col"><p style="margin-bottom:4px"><b>How big the tape is.</b> The number of 1s on the tape (logarithmic scale) against the number of events so far. A straight line here means exponential growth: the tape gains a fixed number of digits per thousand events.</p></div>',
        '<canvas id="qs-chart" role="img" aria-label="number of ones on the tape against events, logarithmic scale"></canvas>',
        '<p style="margin:8px 0 2px"><b>Rules used so far</b></p><div id="qs-tally" style="font-family:var(--mono);font-size:.9em"></div>',
        '<div class="col"><p>Things to notice. Splits and the small cases only move 1s around; an odd round adds 2 and a fold adds half of a block. After <b>+30,000</b> the tape holds more than %s ones. Reaching that tape takes the real machine more steps than that, which is how Lean proves that the machine does not halt in its first %s steps.</p></div>' % (d["kern"], d["kern"]),
        "<script>\n" + read("core.js").split("if(typeof module")[0] + "\n" + read("spec.js") + "\n" + read("widget.js") + "\nQSW(%s,'qs-');\n</script>" % d["var"],
    ]))
    # 4. the cycle
    s.append(dict(id="events-cycle", eyebrow="Emergent behaviour", heading="Cut into quarters, glue back together, grow by half", html=[
        '<div class="col"><p>Seen from far away, the run repeats one pattern at ever larger sizes.</p>'
        '<ol><li><b>One big block.</b> After a fold the tape is a single 1, the head, and one block: <code>1 %s&gt; 0 1<sup>N</sup></code>.</li>'
        '<li><b>Cutting.</b> The block moves to the left of the head and is split: a quarter stays on the left, three quarters go right. The three quarters come back to the head and are split again, and again, leaving a row of pieces, each about three quarters of the one before. The cutting stops when a remainder or a parity does not fit.</li>'
        '<li><b>Gluing.</b> Odd rounds close the gaps between the pieces, and shifts carry the head back to the left.</li>'
        '<li><b>Growing.</b> When an odd block reaches the left end of the tape it is folded: every 2 ones become 3.</li></ol>'
        '<p>%s</p>'
        '<p>The sizes N of these single blocks are %s, &hellip; Each is larger than the last by a factor that is often close to 3/2, but not always, because how many folds and odd rounds happen in between depends on the remainders of the block lengths modulo 4 and on their parities. That is what makes the machine <em>Collatz-like</em>: its future is decided by the low digits of numbers that keep being multiplied by 3/4 and 3/2, and nobody knows how to predict those.</p>'
        '<p>The sister machine <a href="../%s/explainer.html"><code>%s</code></a> does the same thing with a gap of %s 0s for a split instead of %s.</p></div>'
        % (A, d["cycle"], d["folds"], d["twin"], d["twin"], "three" if d["gap"] == 2 else "two", gapw),
    ]))
    # 5. halting
    s.append(dict(id="halting", eyebrow="Halting", heading="What a halt would need", html=[
        '<div class="col"><p>The machine stops only if it reads a 0 in state F. The rules above cover every situation the run has met so far, and none of them halts. But they do not cover every tape one could write down. No rule is given when</p>'
        '<ul><li>the right block is too short for a small case (fewer than 3 ones for <code>zero</code>, fewer than 2 for <code>one</code>%s),</li>'
        '<li>the carrier meets a single 1 standing alone after a single 0, or lands directly on a 1.</li></ul>'
        '<p>Small tapes of these kinds often do halt. For example <code>%s</code> (nothing on the right at all) halts after %d steps, and <code>%s</code> (the carrier meets a lone 1) halts after %d steps. So the machine is not a provable non-halter by its rules alone: it halts if and only if the run ever reaches one of these uncovered tapes and the plain machine then stops.</p>'
        '<p>In the run from blank tape that has not happened in the first %s events. Whether it ever does is the open question.</p></div>'
        % ("" if d["gap"] == 3 else " and <code>two</code>", d["halt1"], d["halt1n"], d["halt2"], d["halt2n"], d["nat_ev"]),
    ]))
    # 6. proved
    s.append(dict(id="proved", eyebrow="Lean", heading="What is proved, and what is not", html=[
        '<div class="col"><ul>'
        '<li><b>Every rule</b>, for every block length and every surrounding tape (Lean kernel): <code>c_split</code>, <code>c_odd</code>, <code>c_fold</code>, <code>c_shift</code>, <code>c_zero</code>, <code>c_one</code>, <code>c_two</code>, <code>c_oneE</code>, <code>c_oneO</code>, <code>c_pass</code> and the carrier&rsquo;s arrival <code>arr_sem</code>, in <code>lean/Events.lean</code>, from single rounds in <code>lean/EventRules.lean</code>.</li>'
        '<li><b>The rules are the machine</b> (kernel): <code>F_sem</code> says that the map F (a rule at an anchor it covers, one plain machine step anywhere else) follows the real machine exactly, and <code>halts_iff</code> says the machine halts from blank tape if and only if repeating F from the blank tape reaches a halting configuration.</li>'
        '<li><b>If the rules never run out, the machine never halts</b> (kernel): <code>events_forever</code>.</li>'
        '<li><b>No halt in the first %s steps</b> (kernel, %s events evaluated inside Lean): <code>no_halt_kernel</code> in <code>lean/Far.lean</code>.</li>'
        '<li><b>No halt in the first %s steps</b> (compiled evaluation, %s events): <code>no_halt_native</code>.</li>'
        '<li><b>This page&rsquo;s JavaScript</b> is a transcription of the Lean definitions. <code>explainer/test.js</code> checks it against the plain machine: every example of the rule viewer, and the first %s events of the run (4&middot;10<sup>8</sup> machine steps).</li>'
        '</ul><p><b>Not proved:</b> that the rules never run out. Nothing here decides whether the machine halts.</p></div>'
        % (d["kern"], d["kern_ev"], d["nat"], d["nat_ev"], d["checked"]),
    ]))
    return s


def claims(d):
    return [
        dict(level="kernel", title="The event rules",
             text="At an anchor (state %s on a single 0 between two blocks of 1s) the machine reaches the next anchor by one of the rules split, odd, fold, shift, zero, one, two (and their variants), each proved for every block length and every surrounding tape." % d["A"],
             where="<code>c_split</code>, <code>c_odd</code>, <code>c_fold</code>, &hellip;, <code>evT_sem</code>, <code>lean/Events.lean</code>"),
        dict(level="kernel", title="Halting is a question about the event map",
             text="The machine halts from blank tape if and only if the orbit of the blank tape under the map F (a rule at every anchor that has one, one machine step otherwise) reaches a halting configuration. If the rules alone can be applied for ever from the first anchor, the machine never halts.",
             where="<code>halts_iff</code>, <code>events_forever</code>, <code>lean/Events.lean</code>"),
        dict(level="kernel", title="No halt in the first %s steps" % d["kern"],
             text="The event orbit is evaluated for %s events by Lean's kernel; the right block is then longer than %s, and a machine started on blank tape needs at least that many steps to write it." % (d["kern_ev"], d["kern"]),
             where="<code>no_halt_kernel</code>, <code>lean/Far.lean</code>"),
        dict(level="native", title="No halt in the first %s steps" % d["nat"],
             text="The same, for %s events, evaluated by compiled code." % d["nat_ev"],
             where="<code>no_halt_native</code>, <code>lean/Far.lean</code>"),
        dict(level="trusted", title="The explainer's event map agrees with the machine",
             text="The JavaScript of the explainer page (a transcription of the Lean definitions) is run against the plain machine: every example of the rule viewer over its whole range, and the first %s events of the run (4&middot;10<sup>8</sup> steps)." % d["checked"],
             where="<code>node holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer/test.js 4e8</code>"),
    ]


def main():
    for d in MACHINES:
        path = os.path.join(HOLD, d["m"], "status.json")
        with open(path) as f:
            st = json.load(f)
        new = claims(d)
        titles = {c["title"] for c in new}
        old = [c for c in st["claims"] if c["title"] not in titles and c["level"] != "open"
               and not c["title"].startswith(("Macro structure", "Parity pattern", "A quarter moves"))]
        st["claims"] = old[:5] + new + old[5:] + [dict(level="open", title="Does it halt from blank tape?", where="",
            text="Not known. A halt needs the event orbit to reach an anchor that no rule covers (a right block that is too short, or the carrier meeting a lone 1) and the machine to stop from there. That has not happened in the first %s events." % d["nat_ev"])]
        st["asof"] = "Status as of 13 November 2026."
        st["family"] = "Collatz-like: blocks split 1:3 by quarters"
        st["summary"] = ("A few huge blocks of 1s. An exact event map is proved in Lean: an even block is split, a quarter to the left and three quarters to the right; "
                         "an odd block at the left end is folded, 2 for 3. The machine halts iff the orbit of this map leaves the rules and stops; no halt in the first %s steps (kernel), %s (compiled). Open."
                         % (d["kern"].replace("<sup>", "^").replace("</sup>", ""), d["nat"].replace("<sup>", "^").replace("</sup>", "")))
        st["verdict"] = [
            "<b>The question is open.</b> The tape is a few huge blocks of 1s, and everything the machine does is arithmetic on their lengths: an even block is split, a quarter going left and three quarters going right; odd blocks are glued to their neighbours; an odd block at the left end is folded, every 2 ones becoming 3.",
            "Lean proves these rules for every size, proves that the machine halts if and only if the orbit of the resulting map reaches a halting configuration, and proves that there is no halt in the first %s steps (%s by compiled evaluation). Whether the rules go on for ever is not known: it depends on remainders modulo 4 of numbers that keep being multiplied by 3/4 and 3/2." % (d["kern"], d["nat"]),
        ]
        ex = st["explainer"]
        ex["lede"] = ("Nobody knows. But what it does is understood exactly: it keeps a few huge blocks of 1s and cuts them into quarters, glues them back and grows them by half, over and over. "
                      "This page lets you watch each of its rules on the real machine and follow its run for tens of thousands of rounds; Lean proves it does not halt in its first %s steps." % d["kern"])
        ex["facts"] = [
            dict(level="kernel", value="%s steps" % d["kern"], text="No halt, proved by Lean's kernel from the event map."),
            dict(level="native", value="%s steps" % d["nat"], text="No halt, by compiled evaluation of the same map."),
            dict(level="kernel", value="exact rules", text="Halting is equivalent to a question about an explicit map on block lengths."),
            dict(level="heuristic", value="Collatz-like", text="Quarters go left, three quarters go right, folds multiply by 3/2."),
        ]
        keep = [x for x in ex["sections"] if x["id"] == "shape"]
        ex["sections"] = sections(d) + keep
        chk = [c for c in st["check"] if "explainer/test.js" not in c]
        st["check"] = chk + ["node holdouts/1RB1LD_1LC0RC_0RF1RA_0LE1LA_1RC0LA_---0RB/explainer/test.js 4e8"]
        with open(path, "w") as f:
            json.dump(st, f, indent=1, ensure_ascii=False)
            f.write("\n")
        print("wrote", path)


if __name__ == "__main__":
    main()
