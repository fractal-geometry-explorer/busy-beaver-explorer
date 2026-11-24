"""Write the section on the digit carry rule into the explainers of both machines.

usage: python3 py/carry_page.py          (then python3 holdouts/build_pages.py M for both machines)

The section (id "carry", after the section "wall" of 1RB---_1LC0RF_1LD0LC_0RE0LF_0RD1LA_1RB0LE) has a widget that
runs the carry table of py/carry.py on the 46 digits, trip by trip or many sweeps at once, and can run the same
sweep on the machine itself in the browser and compare.  The sister machine 1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC
gets a short section pointing to it (after its section "counter").  Running this again replaces both.  It also
rewrites the parts of both status.json files that the carry rule changed (verdict, lede, claims).
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import carry  # noqa: E402

ROOT = os.path.normpath(os.path.join(HERE, "..", ".."))
M1 = carry.M
M2 = "1RB0RA_0LC0RF_0LB1RD_1LE---_1RA0LF_1LE0RC"
AFTER = {M1: "wall", M2: "counter"}
GH = "https://github.com/fractal-geometry-explorer/busy-beaver-explorer/blob/main/holdouts/" + M1

CSS = """
.cr-row{display:flex;gap:3px;overflow-x:auto;padding:8px 2px 4px;scrollbar-width:thin}
.cr-d{display:flex;flex-direction:column;gap:2px;align-items:center;min-width:20px;flex:0 0 auto}
.cr-d i{display:block;width:16px;height:11px;border-radius:2px;background:var(--cell0);border:1px solid var(--line-strong)}
.cr-d i.on{background:var(--ink);border-color:var(--ink)}
.cr-d i.sep{margin-top:3px}
.cr-d.ch i{border-color:var(--head)} .cr-d.ch i.on{background:var(--head);border-color:var(--head)}
.cr-d span{font:10px var(--mono);color:var(--muted)}
.cr-ph{display:flex;gap:3px;flex-wrap:wrap;margin:6px 0}
.cr-ph b{font:500 12px var(--mono);padding:2px 6px;border-radius:4px;background:var(--sunk);color:var(--fg2)}
.cr-ph b.y{color:var(--heur)} .cr-ph b.now{background:var(--accent);color:var(--surface)}
.cr-out{font:13px/1.5 var(--mono);overflow-wrap:anywhere;min-height:3em}
.cr-tab{width:100%;border-collapse:collapse;font-size:.85rem}
.cr-tab th{text-align:left;padding:4px 8px 4px 0;vertical-align:top;font-family:var(--mono)}
.cr-tab td{padding:4px 0;line-height:1.9}
.cr-tab code{display:inline-block;margin:0 3px 0 0;padding:0 3px;border-radius:3px;font-size:.78rem;white-space:nowrap}
.cr-tab code.pass{color:var(--accent)}
.cr-tab code.hit{background:var(--accent-soft);outline:2px solid var(--accent)}
.cr-stats{border-collapse:collapse;font:13px var(--mono)} .cr-stats td,.cr-stats th{padding:2px 10px 2px 0;text-align:right}
.cr-ok{color:var(--kernel);font-weight:600} .cr-bad{color:var(--open);font-weight:600}
"""

JS = r"""
(function(){
var T = __TABLE__, D0 = __WALL0__, H = "__H__", E = "__E__", TAIL = "10001101".repeat(30);
var SK = "x110x110x01100110x110x110", FREE = [0,4,8,17,21], M = "__M__";
var YPH = {1:1, 6:1, 11:1};
var d, p, sweeps, trips, deep, changed, last;
function $(i){ return document.getElementById(i); }
function reset(){ d = D0.slice(); p = 0; sweeps = 0; trips = 0; deep = []; changed = {}; last = ""; draw(); }
function trip(log){
  var c = YPH[p] ? "Y" : "X", j = 0, parts = [];
  while (c){
    if (j >= d.length){ parts.push(c + " passes the last digit"); break; }
    var e = T[c][d[j]];
    if (!e){ parts.push(c + " meets " + d[j] + ": not in the table"); break; }
    parts.push("digit " + j + ": " + c + " " + d[j] + "&gt;" + e[0] + (e[1] ? " passes " + e[1] : " stops"));
    if (log) changed[j] = 1;
    d[j] = e[0]; c = e[1]; j++;
  }
  deep[j] = (deep[j] || 0) + 1; trips++;
  p = (p + 1) % 15; if (p === 0) sweeps++;
  return parts;
}
function act(n, trip1){
  changed = {}; $("crMachSay").innerHTML = "";
  if (trip1){ last = trip(true).join("<br>"); }
  else { for (var k = 0; k < n; k++){ do { trip(n === 1); } while (p !== 0); } last = ""; }
  draw();
}
function draw(){
  var row = "";
  for (var j = 0; j < d.length; j++){
    var s = '<div class="cr-d' + (changed[j] ? ' ch' : '') + '" title="digit ' + j + ': ' + d[j] + '">';
    for (var b = 0; b < 5; b++) s += '<i class="' + (d[j][b] === "1" ? "on" : "") + (b === 3 ? " sep" : "") + '"></i>';
    row += s + "<span>" + j + "</span></div>";
  }
  $("crRow").innerHTML = row;
  var ph = "";
  for (var q = 0; q < 15; q++) ph += '<b class="' + (YPH[q] ? "y " : "") + (q === p ? "now" : "") + '">' + q + (YPH[q] ? " Y" : " X") + "</b>";
  $("crPh").innerHTML = ph;
  $("crPos").innerHTML = "sweep " + sweeps.toLocaleString() + ", trip " + p + " next (carry " + (YPH[p] ? "Y" : "X") + "), " + trips.toLocaleString() + " trips so far";
  $("crOut").innerHTML = last || "&nbsp;";
  var hit = {};
  if (last) last.replace(/: ([XYPQR]) ([01]{5})&gt;/g, function(_, c, x){ hit[c + x] = 1; });
  var cs = document.querySelectorAll("#crTab code");
  for (var i = 0; i < cs.length; i++) cs[i].classList.toggle("hit", !!hit[cs[i].dataset.k]);
  var st = "<tr><th>digits changed &ge; k</th><th>trips</th><th>share</th><th>ratio to k&minus;1</th></tr>", ge = trips, prev = 0;
  for (var k = 1; k < deep.length; k++){
    st += "<tr><td>" + k + "</td><td>" + ge.toLocaleString() + "</td><td>" + (trips ? (ge / trips).toPrecision(4) : "") + "</td><td>" + (k > 1 && ge ? (prev / ge).toFixed(3) : "") + "</td></tr>";
    prev = ge; ge -= deep[k] || 0; if (!ge) break;
  }
  $("crStats").innerHTML = trips ? st : "";
  $("crMach").disabled = p !== 0;
}
function wall(dd){
  var w = H;
  for (var j = 0; j < dd.length; j++){
    var x = SK.split(""); for (var k = 0; k < 5; k++) x[FREE[k]] = dd[j][k]; w += x.join("");
  }
  return w + E + TAIL;
}
function machine(){
  var tr = M.split("_").map(function(s){ return [s.slice(0,3), s.slice(3,6)]; });
  var w = wall(d), s = "0" + "01101".repeat(3) + w, tape = {}, h = 0, st = 2, steps = 0, lo = 0;
  for (var i = 0; i < s.length; i++) tape[i] = +s[i];
  while (true){
    var t = tr[st][tape[h] || 0];
    if (t[2] === "-"){ return {halt: steps}; }
    tape[h] = +t[0]; h += t[1] === "R" ? 1 : -1; st = t.charCodeAt(2) - 65; steps++;
    if (h < lo) lo = h;
    if (st === 2 && h === lo && steps > 10) break;
  }
  var hi = s.length - 1, out = "";
  for (var q = hi - w.length + 1; q <= hi; q++) out += tape[q] || 0;
  return {steps: steps, wall: out};
}
$("crTrip").onclick = function(){ act(1, true); };
$("crSweep").onclick = function(){ act(1, false); };
$("crS100").onclick = function(){ act(100, false); };
$("crS10k").onclick = function(){ act(10000, false); };
$("crReset").onclick = reset;
$("crMach").onclick = function(){
  var before = d.slice(), r = machine();
  act(1, false);
  var model = wall(d);
  if (r.halt !== undefined) $("crMachSay").innerHTML = '<span class="cr-bad">the machine halted after ' + r.halt + ' steps</span>';
  else $("crMachSay").innerHTML = "The machine ran this sweep in " + r.steps.toLocaleString() + " steps. Its wall is " +
    (r.wall === model ? '<span class="cr-ok">the same, all 1,573 cells,</span>' : '<span class="cr-bad">different</span>') + " as the one the table gives.";
};
reset();
})();
"""


def table_html():
    rows = []
    for c in carry.CARRIES:
        cells = []
        for x, (x2, c2) in sorted(carry.TABLE[c].items()):
            cells.append(f'<code data-k="{c}{x}"' + (' class="pass"' if c2 else '') + f'>{x}&gt;{x2}'
                         + (f':{c2}' if c2 else '') + '</code>')
        rows.append(f'<tr><th>{c}</th><td>{"".join(cells)}</td></tr>')
    return '<table class="cr-tab" id="crTab">' + ''.join(rows) + '</table>'


def section_m1():
    *_, (s, w) = carry.walls(3e9)
    w0 = next(iter(carry.walls(3e9)))[1]
    js = (JS.replace('__TABLE__', json.dumps({c: {x: [a, b] for x, (a, b) in carry.TABLE[c].items()}
                                              for c in carry.CARRIES}, separators=(',', ':')))
          .replace('__WALL0__', json.dumps(carry.digits(w0)))
          .replace('__H__', carry.H).replace('__E__', w0[1194:1333]).replace('__M__', M1))
    html = f"""<style>{CSS}</style>
<div class="col">
<p>The wall is now decoded. Write it as <code>H D<sub>0</sub> D<sub>1</sub> &hellip; D<sub>45</sub> E (10001101)<sup>30</sup></code>:
a head part <code>H</code> of 44 cells that is the same at every sweep, 46 <b>digits</b> of 25 cells, an end part
<code>E</code> of 139 cells, and the words at the far end. Every digit has the form
<code>a110 b110 c011 0011 0d11 0e11 0</code>, so it is five free cells <code>a b c d e</code>; below, each digit is a
column of five squares, <code>a</code> at the top.</p>
<p>Between two visits to the left end the head does not make one pass over the counter but <b>15 trips</b>: from
<code>H</code> into the digits and back. <code>H</code> is a fixed sequencer: trip 1, 6 and 11 of every sweep feed
the carry <b>Y</b> into digit 0, the other twelve feed <b>X</b>. A carry that reaches a digit rewrites it and either
stops or passes a carry on to the next digit, and five carries occur: X, Y, P, Q, R. That is the whole rule: one
table of 73 entries. X is binary counting in <code>a b c</code> (a lowest); when all three are 1 the digit overflows,
and <code>d e</code> records how often it has (11 &rarr; 01 &rarr; 10), which decides the carry passed on.</p>
</div>
<div class="panel">
  <div class="cr-ph" id="crPh"></div>
  <div class="cr-row" id="crRow" aria-label="the 46 digits"></div>
  <p class="small" id="crPos"></p>
  <div class="controls">
    <button class="primary" id="crTrip">One trip</button><button id="crSweep">One sweep</button>
    <button id="crS100">100 sweeps</button><button id="crS10k">10,000 sweeps</button><button id="crReset">Back to step 20,018,306</button>
    <button id="crMach">Run the next sweep on the machine</button>
  </div>
  <p class="small" id="crMachSay" aria-live="polite"></p>
  <div class="cr-out" id="crOut" aria-live="polite"></div>
  <h3>The table</h3>
  <p class="small"><code>d&gt;d'</code>: the carry turns digit d into d' and stops; <code>d&gt;d':c</code>: &hellip; and passes c on
  (blue). The entries of the last trip are outlined.</p>
  {table_html()}
  <h3>How deep the carries go</h3>
  <table class="cr-stats" id="crStats"></table>
</div>
<div class="col">
<p>The digits start as they were at step 20,018,306. Step through a few trips, then run 10,000 sweeps and look at
the counts: a quarter of all trips go past digit 0, and from digit 4 on each digit is reached by 3/8 of the trips
that reach the one before (the ratio column settles at 2.667). The button <em>Run the next sweep on the machine</em>
runs the Turing machine itself on the same wall, 5,000 to 15,000 steps, and compares the wall it leaves with the
table's.</p>
<p>What is established, and how. The table reproduces every one of the 4,500 trips of the first 300 sweeps and
every one of the 29,299 sweeps from step 2&middot;10<sup>7</sup> to 2&middot;10<sup>10</sup>, simulated in C and Python
(<a href="{GH}/py/carry.py"><code>py/carry.py</code></a>): computed, not proved. Lean proves, kernel only, that the
table never needs an entry it does not have: on the strings of digits whose neighbours are among 240 allowed pairs
(and whose digit 0 is one of 8 values for each trip), every trip lands on such a string again, for strings of any
length, and the 46 digits of step 20,018,306 are such a string (<a href="{GH}/lean/Carry.lean"><code>lean/Carry.lean</code></a>,
<code>trip_good</code>, <code>wall0_never_stuck</code>). That is a theorem about the table, not yet about the machine.</p>
<p>At 3/8 per digit the carries pass digit 45 about once in 6&middot;10<sup>19</sup> trips, near 10<sup>38</sup> steps.
Forcing carries into <code>E</code> on made-up walls (<a href="{GH}/py/endregion.py"><code>py/endregion.py</code></a>)
shows that <code>E</code> is more counter in a fresh form (its cells 0, 4, 8 count in binary), and that after 56 such
carries it is rewritten and the far end grows by one word: no halt in 400 of them. What the run does when its own
carries get there is the open question.</p>
</div>
<script>{js}</script>"""
    return {"id": "carry", "eyebrow": "The counter, decoded", "heading": "The digit carry rule", "html": html}


def section_m2():
    html = f"""<div class="col">
<p>This machine's run is the run of <a href="../{M1}/explainer.html#carry"><code>{M1}</code></a> in a mirror, with
one more word at the far end (proved: see the sections below). So its counter is that machine's counter read right
to left: each 25-cell digit <code>11a0 11b0 1100 110c 0 11d0 11e0</code> here is a digit
<code>a110 b110 c011 0011 0d11 0e11 0</code> there read right to left (its free cells a, b, c, d, e are e, d, c, b, a
here), and the decoded carry rule there, a 15-trip sweep and
a table of 73 entries that reproduces every sweep to 2&middot;10<sup>10</sup> steps, is the rule here.
<a href="../{M1}/explainer.html#carry">That page</a> lets you run it.</p>
</div>"""
    return {"id": "carry", "eyebrow": "The counter, decoded", "heading": "The digit carry rule (on the sister page)",
            "html": html}


VERDICT = ("<b>The question is open.</b> The head bounces between a block that grows at the left end and a wall of "
           "exactly 1,573 cells at the right end. The wall is a counter, now decoded: 46 digits of 25 cells, 15 trips "
           "of the head per sweep and a carry table of 73 entries, which reproduces every sweep to 2&middot;10<sup>10</sup> "
           "steps. The carries reach the end of the wall only near 10<sup>38</sup> steps; what happens then is the question.")

CLAIMS = [
    {"level": "trusted", "title": "The digit carry rule",
     "text": "The wall is a head part of 44 cells, 46 digits <code>a110 b110 c011 0011 0d11 0e11 0</code> and an end "
             "part of 139 cells. Each sweep is 15 trips from the head part into the digits; trips 1, 6, 11 feed carry Y, "
             "the others carry X, and a table of 73 entries (carries X, Y, P, Q, R) gives what a carry does to a digit. "
             "The table reproduces all 4,500 trips of the first 300 sweeps (machine simulated step by step) and all "
             "29,299 sweeps from 2&middot;10<sup>7</sup> to 2&middot;10<sup>10</sup> steps.",
     "where": "<code>python3 py/carry.py trips 300</code>, <code>python3 py/carry.py check</code>"},
    {"level": "kernel", "title": "The carry table never gets stuck (a theorem about the model)",
     "text": "On digit strings whose neighbours are among 240 allowed pairs, each trip of the table lands on such a "
             "string again and never meets a pair (carry, digit) outside the 73 entries, for strings of every length; "
             "from the 46 digits of the wall at step 20,018,306 the table never gets stuck, at any number of trips, until "
             "a carry runs off the last digit. About the table only: its link to the machine is the simulation above.",
     "where": "<code>trip_good</code>, <code>wall0_never_stuck</code>, <code>lean/Carry.lean</code>"},
    {"level": "heuristic", "title": "When the carries reach the end of the wall",
     "text": "In 10<sup>6</sup> sweeps of the table, a quarter of the trips pass digit 0 and from digit 4 on each digit "
             "is reached by 3/8 of the trips that reach the one before. At that rate the carries pass digit 45 about once "
             "in 6&middot;10<sup>19</sup> trips, near 10<sup>38</sup> steps. Forced carries on made-up walls show the end "
             "part counting in a fresh form and, after 56 carries, rewritten with the far end one word longer; no halt "
             "in 400.",
     "where": "<code>python3 py/carry.py far 1e6</code>, <code>python3 py/endregion.py</code>"},
]

CLAIM_M2 = {"level": "trusted", "title": "The digit carry rule (from the sister machine)",
            "text": "By the proved correspondence of the two runs, this machine's counter is the decoded counter of "
                    f"<code>{M1}</code> in a mirror: 15 trips per sweep and a carry table of 73 entries that reproduces "
                    "every sweep of that run to 2&middot;10<sup>10</sup> steps.",
            "where": f"<code>holdouts/{M1}/py/carry.py</code>"}


def put_section(d, m, sec):
    secs = [s for s in d["explainer"]["sections"] if s["id"] != "carry"]
    at = next(i for i, s in enumerate(secs) if s["id"] == AFTER[m]) + 1
    d["explainer"]["sections"] = secs[:at] + [sec] + secs[at:]


def put_claims(d, new):
    titles = {c["title"] for c in new}
    cl = [c for c in d["claims"] if c["title"] not in titles]
    at = next((i for i, c in enumerate(cl) if c["level"] == "open"), len(cl))
    d["claims"] = cl[:at] + new + cl[at:]


def main():
    for m in (M1, M2):
        p = os.path.join(ROOT, m, "status.json")
        with open(p) as f:
            d = json.load(f)
        if m == M1:
            put_section(d, m, section_m1())
            put_claims(d, CLAIMS)
            d["verdict"] = [VERDICT]
            d["explainer"]["lede"] = (VERDICT.replace("<b>The question is open.</b>", "Nobody knows.") +
                                      " It is proved to share that question with <code>" + M2 +
                                      "</code>: one halts exactly when the other does.")
            for s in d["explainer"]["sections"]:
                if s["id"] == "wall" and isinstance(s["html"], list) and len(s["html"]) == 3:
                    s["html"][2] = ("<p>About 46 such digits are in the wall. The next section decodes them: the exact "
                                    "carry rule, which you can run.</p>")
            facts = [f for f in d["explainer"]["facts"] if "73" not in f["value"]]
            facts.insert(1, {"level": "trusted", "value": "73 entries",
                             "text": "the carry table of the counter, checked on every sweep to 2&middot;10<sup>10</sup> "
                                     "steps (<a href=\"#carry\">below</a>)."})
            d["explainer"]["facts"] = facts
            d["summary"] = ("A bouncer between a growing block and a wall of exactly 1,573 cells that is a counter of 46 "
                            "digits, decoded: 15 trips per sweep and a carry table of 73 entries (checked to "
                            "2&middot;10<sup>10</sup> steps, never stuck by a Lean proof about the table); the carries "
                            "reach the end of the wall near 10<sup>38</sup> steps and what happens then is unknown.")
        else:
            put_section(d, m, section_m2())
            put_claims(d, [CLAIM_M2])
        d["asof"] = "Status as of 24 November 2026."
        with open(p, "w") as f:
            json.dump(d, f, indent=1, ensure_ascii=False)
            f.write("\n")
        print("wrote", p)


if __name__ == "__main__":
    main()
