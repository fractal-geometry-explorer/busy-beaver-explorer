"""Family F05 (the nested block counter on one shared core): write the family's part of every member's records.

For each of the 40 machines of frames.FAMILY, and for the 5 related machines of OTHER, this adds to
holdouts/M/status.json and holdouts/M/README.md (and replaces what an earlier run of this script added):

* an explainer section `f05` ("One core, forty machines"): the machine's place in the family, the run seen from the
  left end as a list of blocks (a slider over the left-end events of data/f05_run.json), the table of the sixteen
  (D1, F0) variants, and why the question is still open;
* claims tagged `"tag": "F05"`: the conjugacy to the frame-A core (`halts_iff`), the visit rule and closed form on the
  machine's own table, what a clean visit conserves (`visit_conserves`), the run of f05_run.py, and the heuristic on
  drifts;
* a README block between `<!-- F05 -->` markers.

The records of the 14 machines of the first pass are written by write_records.py first; this script only adds to
them.  Run build_pages.py afterwards.

usage: python3 f05_records.py [MACHINE ...]      (default: all 45)
"""
import html
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
HOLD = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)
import frames  # noqa: E402

LEAD = frames.FAMILY[0][0]
SHARED = f"holdouts/{LEAD}"
ASOF = "Status as of 13 November 2026."
CORE = "1RB0LC_0RC0RB_1LD0RE_0LE?LF_1LA0LB_??---"
FIRST = {r[0] for r in frames.FIRST}

# Holdouts of the family plan whose table is not a renaming of the core: (machine, the family member whose tapes its
# run shares, what the earlier passes observed).  Nothing here is proved.
OTHER = [
    ("1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF", "1RB0LC_0RC1RF_1RD0RE_1LE0RA_0LA0LE_1RE---",
     "its run has the tape and head of a configuration of the other run for 8,330,203 of its first 10<sup>7</sup> "
     "steps, in the same order (<code>holdouts/related.py</code>, relation &ldquo;same tapes, another pace&rdquo;)"),
    ("1RB0RC_1LC0RD_0LD0LC_1RE0LA_0LE1RF_0RA---", "1RB---_0LC0LB_1RF0LD_1RE0RB_1LB0RC_0RD1RA",
     "its run has the tape and head of a configuration of the other run for 8,330,405 of its first 10<sup>7</sup> "
     "steps, in the same order (<code>holdouts/related.py</code>, relation &ldquo;same tapes, another pace&rdquo;)"),
    ("1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---",
     "the first pass found the same tape at every sweep end up to 10<sup>11</sup> steps (the mirrored members from "
     "sweep 157,376 on, with a different first block)"),
    ("1RB0LC_0RC0RB_1LD0RE_0LE0LB_1LA1RF_0LD---", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---",
     "the first pass found the same tape at every sweep end up to 10<sup>11</sup> steps"),
    ("1RB0LC_0RC0RE_1RD1LF_1LE0RA_0LA0LE_0RB---", "1RB0LC_0RC0RB_1LD0RE_0LE1LF_1LA0LB_0RE---",
     "the first pass found the same tape at every sweep end up to 10<sup>11</sup> steps (the mirrored members from "
     "sweep 157,376 on, with a different first block)"),
]


def d1(fa):
    return fa.split("_")[3][3:]


def f0(fa):
    return fa.split("_")[5][:3]


def load_run(m):
    p = os.path.join(HOLD, m, "data", "f05_run.json")
    return json.load(open(p)) if os.path.exists(p) else None


def link(m, here, text=None, md=False):
    t = text or m
    if m == here:
        return f"**{t}**" if md else f"<b>{t}</b>"
    return f"[{t}](../{m}/README.md)" if md else f'<a href="../{m}/explainer.html">{t}</a>'


def pow10(s):
    """'10^k' form of a decimal string: the power of ten it has reached"""
    return len(s) - 1


def sci(s, md=False):
    k = len(s) - 1
    lead = s[0] + ("." + s[1] if len(s) > 1 else "")
    return f"{lead}·10^{k}" if md else f"{lead}&middot;10<sup>{k}</sup>"


def steps_html(e):
    """'3e+09' -> 3&middot;10<sup>9</sup>"""
    a, b = e.split("e")
    return f"{a}&middot;10<sup>{int(b)}</sup>"


def variants():
    """rows of the variant table: (D1, F0) -> [(machine, frame, start, run)]"""
    rows = {}
    for m, fr, fa, st in frames.FAMILY:
        rows.setdefault((d1(fa), f0(fa)), []).append((m, fr, st, load_run(m)))
    return rows


def run_classes():
    """machines whose last left-end event (step and first blocks) is the same: a letter per class (observed)"""
    cl = {}
    for m, fr, fa, st in frames.FAMILY:
        r = load_run(m)
        if r and r.get("last_left_end") and not r["halted"]:
            k = (r["target_steps"], r["last_left_end"]["step"], tuple(r["last_left_end"]["first_blocks"]))
            cl.setdefault(k, []).append(m)
    names = {}
    i = 0
    for k, ms in cl.items():
        if len(ms) > 1:
            for m in ms:
                names[m] = "abcdefghijklmnopqrstuvwxyz"[i]
            i += 1
    return names


def result_text(r, md=False):
    if r is None:
        return "not run"
    if r["halted"]:
        return f"HALTS at step {r['halted']}"
    k = r["steps_digits"] - 1
    p = f"10^{k}" if md else f"10<sup>{k}</sup>"
    return f"no halt in {p} steps, {r['f_events']} F-events, all reading 0"


def variant_table(here, md=False):
    rows = variants()
    cls = run_classes()
    out = []
    for (w, f), ms in sorted(rows.items()):
        for m, fr, st, r in ms:
            c = cls.get(m, "")
            res = result_text(r, md)
            if md:
                name = f"**`{m}`**" if m == here else f"[`{m}`](../{m}/README.md)"
                out.append(f"| {w} | {f} | {name} | {fr} | {st} | {c} | {res} |")
            else:
                out.append(f"<tr><td>{w}</td><td>{f}</td><td><code>{link(m, here)}</code></td><td>{fr}</td>"
                           f"<td>{st}</td><td>{c}</td><td>{res}</td></tr>")
    if md:
        return ("| D1 | F0 | machine | frame | frame-A start | same run | exact block-list map |\n"
                "|---|---|---|---|---|---|---|\n" + "\n".join(out))
    return ('<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>D1</th><th>F0</th><th>machine</th>'
            '<th>frame</th><th>frame-A start</th><th>same run</th><th>exact block-list map</th></tr></thead><tbody>'
            + "".join(out) + "</tbody></table></div>")


WIDGET_JS = r"""
(function(){
  var D = JSON.parse(document.getElementById('f05data').textContent);
  var ev = D.events, sl = document.getElementById('f05slider'), box = document.getElementById('f05bars'),
      cap = document.getElementById('f05cap'), timer = null;
  sl.max = ev.length - 1;
  function big(s){ return BigInt(s); }
  function short(s){ return s.length <= 9 ? s.replace(/\B(?=(\d{3})+(?!\d))/g, ',') : s[0] + '.' + s.slice(1,3) + '·10^' + (s.length-1); }
  function draw(){
    var k = +sl.value, e = ev[k], b = e.blocks, n = b.length, rows = [], best = -1, bestLife = null;
    var lives = b.map(function(x, i){
      if (i === 0 || i === n - 1) return null;
      var rate = 18n * (5n ** BigInt(i - 1));
      return big(x) / rate;
    });
    lives.forEach(function(l, i){ if (l !== null && (bestLife === null || l < bestLife)) { bestLife = l; best = i; } });
    var maxLen = 1;
    b.forEach(function(x){ if (x.length > maxLen) maxLen = x.length; });
    b.forEach(function(x, i){
      var w = Math.max(2, Math.round(100 * (x.length - 1 + Math.log10(+x[0] + (x.length > 1 ? +x[1] / 10 : 0) + 0.0001)) / Math.max(1, maxLen)));
      if (!(w > 2)) w = 2;
      var kind = i === 0 ? 'first' : (i === n - 1 ? 'last' : (i === best ? 'next' : 'mid'));
      var col = {first: 'var(--muted)', last: 'var(--kernel)', next: 'var(--head)', mid: 'var(--accent)'}[kind];
      var note = i === 0 ? 'first block (the left end works on it directly)'
        : i === n - 1 ? 'last block: grows'
        : 'loses 18·5^' + (i - 1) + ' a visit: ' + short(String(lives[i])) + ' visits left' + (i === best ? ' ← runs out first' : '');
      rows.push('<div style="display:flex;align-items:center;gap:8px;margin:2px 0;font:12px var(--mono)">'
        + '<span style="width:2.2em;text-align:right;color:var(--muted)">b' + (i + 1) + '</span>'
        + '<span style="flex:0 0 38%;background:var(--sunk);height:12px;position:relative"><span style="position:absolute;left:0;top:0;bottom:0;width:' + w + '%;background:' + col + '"></span></span>'
        + '<span style="width:9.5em;text-align:right;color:var(--fg)">' + short(x) + '</span>'
        + '<span style="color:var(--fg2)">' + note + '</span></div>');
    });
    box.innerHTML = rows.join('');
    cap.textContent = 'left-end event ' + (k + 1) + ' of ' + ev.length + ' shown (' + D.total + ' in the whole run) · step '
      + short(e.step) + ' · ' + n + ' block' + (n === 1 ? '' : 's') + ' · bars on a logarithmic scale';
  }
  sl.addEventListener('input', draw);
  document.getElementById('f05prev').addEventListener('click', function(){ sl.value = Math.max(0, +sl.value - 1); draw(); });
  document.getElementById('f05next').addEventListener('click', function(){ sl.value = Math.min(ev.length - 1, +sl.value + 1); draw(); });
  document.getElementById('f05play').addEventListener('click', function(){
    if (timer) { clearInterval(timer); timer = null; this.textContent = 'Play'; return; }
    var btn = this; btn.textContent = 'Stop';
    if (+sl.value >= ev.length - 1) sl.value = 0;
    timer = setInterval(function(){
      if (+sl.value >= ev.length - 1) { clearInterval(timer); timer = null; btn.textContent = 'Play'; return; }
      sl.value = +sl.value + 1; draw();
    }, 350);
  });
  sl.value = Math.min(ev.length - 1, 24);
  draw();
})();
"""


def widget(r):
    data = {"events": [{"step": e["step"], "blocks": e["blocks"]} for e in r["left_end"] if e["blocks"]],
            "total": r["left_end_events"]}
    return (
        '<div class="panel"><div class="controls">'
        '<button id="f05prev" type="button">&larr;</button>'
        '<input id="f05slider" type="range" min="0" max="1" value="0" step="1" style="flex:1;min-width:160px" '
        'aria-label="left-end event">'
        '<button id="f05next" type="button">&rarr;</button>'
        '<button id="f05play" class="primary" type="button">Play</button></div>'
        '<div class="cap" id="f05cap"></div><div id="f05bars" style="margin-top:8px"></div></div>'
        '<script type="application/json" id="f05data">' + json.dumps(data, separators=(",", ":")) + "</script>"
        "<script>" + WIDGET_JS + "</script>")


def frame_sentence(m, fr, fa, st):
    mp = frames.frame_map(fr)
    if fr == "A":
        return (f"This machine is the core itself (frame A) with D1 = {d1(fa)} and F0 = {f0(fa)}, started in state "
                f"{st}.")
    ren = ", ".join(f"{s}&rarr;{mp[s]}" for s in frames.STATES)
    return (f"This machine is the <b>mirror image</b> (left and right exchanged) of the core with D1 = {d1(fa)} and "
            f"F0 = {f0(fa)}, that is of <code>{fa}</code>, with the states renamed {ren} (frame {fr}); its start "
            f"state A is the core's state {st}. So its run from blank tape is, step for step and mirrored, the run "
            f"of <code>{fa}</code> started in state {st} on blank tape, and the block lists below read right to left "
            f"on this machine's own tape.")


def drift_text(r):
    d = r["drift"]
    a, b = d.get("smallest_after_1e20"), d.get("smallest_after_1e100")
    parts = []
    if a:
        parts.append(f"after step 10<sup>20</sup> the smallest drift in absolute value is {int(a):,}")
    if b:
        parts.append(f"after step 10<sup>100</sup> it is {int(b):,}")
    return ", ".join(parts)


def section(m):
    fr, fa, st = frames.info(m)
    r = load_run(m)
    k = r["steps_digits"] - 1
    ctx = "; ".join(f"<code>{html.escape(c['context'])}</code> ({c['count']}&times;, F reads {c['reads']})"
                    for c in r["f_contexts"])
    raw = r["simulator"] == "hybrid2.py"
    rawtxt = (", here on the raw tape where the F-event leaves a gadget <code>0 1</code> between two blocks"
              if raw else "")
    v = r.get("validated")
    valtxt = ("was checked against the plain simulation of the machine on the F-events of the first "
              + steps_html(v["direct_steps"]) + " steps") if v and v.get("match") else "is exact by construction"
    h = [
        "<p>This machine is one of <b>40 holdouts built on the same five states</b>. Written in one common frame "
        "(frame A), every one of them has the table</p>"
        "<div style=\"overflow-x:auto\"><table class=\"tbl\"><thead><tr><th>state</th><th>A</th><th>B</th><th>C</th>"
        "<th>D</th><th>E</th><th>F</th></tr></thead><tbody><tr><td>reads 0</td><td>1RB</td><td>0RC</td><td>1LD</td>"
        "<td>0LE</td><td>1LA</td><td><b>F0</b></td></tr><tr><td>reads 1</td><td>0LC</td><td>0RB</td><td>0RE</td>"
        "<td><b>0LF or 1LF</b></td><td>0LB</td><td>halt</td></tr></tbody></table></div>"
        "<p>and they differ in three things only: the bit that D writes on its way into F (D1), what F does on a 0 "
        "(F0), and the state the run starts in. " + frame_sentence(m, fr, fa, st) + " Lean proves this for the "
        "machine's own table (<code>halts_iff</code> in <code>lean/Family.lean</code>): it halts from blank tape "
        f"exactly if the frame-A table halts from blank tape in state {st}.</p>",
        "<p><b>What the 40 machines share.</b> States A to E never enter F while they run the nested counter, so "
        "between two entries into F all 40 machines do the same thing, and one law covers them. In frame A the tape "
        "is a list of blocks <code>(10)^b</code>; a <em>visit</em> to the list [b<sub>1</sub>, &hellip;, "
        "b<sub>k</sub>] makes five visits to the list without its first block. When the blocks are large and of the "
        "right parity (a <em>clean</em> visit) this has a closed form: b<sub>1</sub> loses 5, block i loses "
        "18&middot;5<sup>i&minus;2</sup>, the last block gains 12&middot;5<sup>k&minus;2</sup>. Both the recursion "
        "and the closed form are Lean theorems for every depth, on each of the 40 tables (<code>go_spec</code>, "
        "<code>go_closed</code>). Two quantities are therefore <b>conserved by every clean visit</b> "
        "(<code>visit_conserves</code>): the residue of block i modulo 18&middot;5<sup>i&minus;2</sup>, and the "
        "<em>drift</em> b<sub>i+1</sub> &minus; 5&middot;b<sub>i</sub> of two neighbouring blocks (neither the "
        "first nor the last). The residue fixes at which phase and with which small value a block will run out; the "
        "drift is the length the next block still has at that moment.</p>",
        "<p><b>This machine's run, seen from the left end.</b> Each time the head comes back to the left end of the "
        "tape (frame A) the tape is a plain list of blocks. Move the slider through these moments: the middle "
        "blocks drain at their fixed rates, the last block grows, a block that runs out disappears and its "
        "neighbours merge, and new blocks are born at the right end. The list is from the exact block-list map "
        "(below), which " + valtxt + ".</p>",
        widget(r),
        "<p><b>How far it has been run.</b> The exact block-list map (clean visits by the proved closed form, every "
        "other visit by an exact run-length simulation" + rawtxt + ") "
        f"runs this machine for {sci(r['steps'])} steps without a halt: {r['left_end_events']} "
        f"returns to the left end, {r['f_events']} entries into F, every one reading 0, with the tape around the "
        f"head {ctx}. Every one of these entries is the kind proved harmless in Lean (<code>fevent</code>, "
        "<code>fevent_reads_zero</code>): a visit ends in state C on the 0 of a phase-1 tail, and F then reads the "
        "last cell of a <code>1000</code>.</p>",
        "<p><b>The sixteen variants.</b> The 40 machines are 16 choices of (D1, F0), each from up to three start "
        "states. Machines marked with the same run letter had exactly the same block list at their last left-end "
        "event (an observation, not a proof); they are still separate halting questions until that is proved."
        "</p>" + variant_table(m),
        "<p><b>Why this does not settle halting.</b> A clean visit cannot halt, and an isolated exceptional event "
        "(one block running out between long neighbours, a birth, the harmless F-event) does not halt in any run "
        "so far. Short block lists of the same shape do halt, so a proof has to control the block lengths: it "
        "would have to show that two exceptional events never fall close together, that is, that a drift is never "
        "small when its block runs out. The drifts only change at exceptional events, where they are sums and "
        "differences of large earlier blocks; nothing is known that keeps them away from 0. "
        + (f"Observed in this run, at the left-end events: {drift_text(r)}. " if drift_text(r) else "")
        + "That is evidence, not a proof, and it is sampled at the left-end events only.</p>",
    ]
    return {"id": "f05", "eyebrow": "The family", "heading": "One core, forty machines", "html": h}


def claims(m):
    fr, fa, st = frames.info(m)
    r = load_run(m)
    mp = frames.frame_map(fr)
    out = [
        {"level": "kernel", "tag": "F05", "title": "One of 40 holdouts on the same five-state core",
         "text": (f"In frame A all 40 machines have states A to E of <code>{CORE}</code> and differ in D1 (0LF or "
                  f"1LF), in F0 and in the start state. "
                  + ("This machine is that table itself" if fr == "A" else
                     "This machine is the mirror image of that table with the states renamed "
                     + ", ".join(f"{s}&rarr;{mp[s]}" for s in frames.STATES))
                  + f", with D1 = {d1(fa)} and F0 = {f0(fa)}: <code>step_img</code> proves that every step of the "
                  f"machine is a step of <code>{fa}</code>, and <code>halts_iff</code> that it halts from blank "
                  f"tape if and only if <code>{fa}</code> halts from blank tape started in state {st}. The tables "
                  "of all 40 are compared by <code>frames.py</code>."),
         "where": f"<code>step_img</code>, <code>halts_iff</code>, <code>lean/Family.lean</code>; "
                  f"<code>{SHARED}/py/frames.py</code>"},
    ]
    if m not in FIRST:
        out.append(
            {"level": "kernel", "tag": "F05", "title": "The family's visit rule and its closed form",
             "text": ("In frame A a <em>visit</em> starts with the head in state A on the 0 in front of plain blocks "
                      "<code>(10)^b1 1 (10)^b2 1 &#8230; 1</code> and ends when the head first steps left of that "
                      "cell. <code>go_spec</code> proves for every depth that a clean visit turns the list l into "
                      "<code>go n l</code> in exactly <code>goT n l</code> steps (the first block is spread, the "
                      "rest gets five visits, the first block is folded back 5 shorter); <code>go_closed</code> "
                      "gives the closed form (b1&minus;5, b2&minus;18, b3&minus;90, &#8230;, "
                      "b<sub>k</sub>+12&middot;5<sup>k&minus;2</sup>) when b1 is odd and at least 7, the other "
                      "blocks even and block i at least 2+18&middot;5<sup>i&minus;2</sup>. <code>visit</code> "
                      "states it as a run of this machine. Also proved: the birth of a block, and that the entry "
                      "into F after a visit that ends in state C on a phase-1 tail reads a 0 "
                      "(<code>fevent</code>, <code>fevent_reads_zero</code>). The proofs are generated for this "
                      "machine's own frame-A table; they never use F0."),
             "where": "<code>go_spec</code>, <code>go_closed</code>, <code>visit_closed</code>, <code>visit</code>, "
                      "<code>birth</code>, <code>fevent_reads_zero</code>, <code>lean/Family.lean</code> (written by "
                      f"<code>{SHARED}/py/gen_family_lean.py</code>)"})
    out.append(
        {"level": "kernel", "tag": "F05", "title": "What a clean visit conserves",
         "text": ("For the blocks after the first, the last one left out: a clean visit (a list the closed form "
                  "applies to) changes neither the residue of block i modulo 18&middot;5<sup>i&minus;2</sup> nor "
                  "the drift b<sub>i+1</sub> &minus; 5&middot;b<sub>i</sub> of two neighbours. So these numbers "
                  "change only at the exceptional events (a block running out, a birth, an entry into F, the left "
                  "end). This is a law between events, not a proof that the machine never halts."),
         "where": "<code>tailEff_res</code>, <code>tailEff_drift</code>, <code>visit_conserves</code>, "
                  "<code>lean/Family.lean</code>"})
    if r:
        k = r["steps_digits"] - 1
        v = r.get("validated")
        val = (f" Its F-events (step and cell read) agree with the plain cell-by-cell simulation of the machine on "
               f"the first {steps_html(v['direct_steps'])} steps ({v['f_events']} F-events).") if v and v["match"] else ""
        ctx = "; ".join(f"<code>{html.escape(c['context'])}</code> ({c['count']}&times;)" for c in r["f_contexts"])
        out.append(
            {"level": "trusted", "tag": "F05",
             "title": f"No halt in the first {sci(r['steps'])} steps (exact block-list map)",
             "text": (f"The machine run as a map on block lists (clean visits by the closed form, a Lean theorem; "
                      f"every other visit by the exact run-length simulator, memoised) reaches step {sci(r['steps'])} "
                      f"without a halt: {r['left_end_events']} returns to the left end, {r['f_events']} entries "
                      f"into F, all reading 0, all with the tape of the proved harmless kind around the head "
                      f"({ctx}). The list has {r['blocks_at_end']} blocks at the last left-end event." + val
                      + (" This machine's F0 leaves a gadget <code>0 1</code> between two blocks after an F-event, "
                         "so lists with the gadget are simulated on the raw tape, which is slower: hence the "
                         "smaller step count." if r["simulator"] == "hybrid2.py" else "")),
             "where": f"<code>data/f05_run.json</code>, <code>{SHARED}/py/f05_run.py</code> "
                      f"(<code>{r['simulator']}</code>)"})
        dt = drift_text(r)
        out.append(
            {"level": "heuristic", "tag": "F05", "title": "Halting would need two exceptional events close together",
             "text": ("A clean visit cannot halt, and in the runs every exceptional event with long blocks around "
                      "it ends without a halt; short lists of the same shape do halt. When block i runs out, the "
                      "next block has about the length of their drift, so a second event close by needs a drift "
                      "near 0 at that moment. " + (f"Observed at the left-end events of this run: {dt}. " if dt else "")
                      + "New drifts are made of sums and differences of earlier blocks, which grow with the run, "
                      "so close pairs of events should become ever rarer; but nothing proved keeps a drift away "
                      "from 0, and the figures are sampled at the left-end events only."),
             "where": f"<code>data/f05_run.json</code> (<code>drift</code>), <code>{SHARED}/py/f05_run.py</code>"})
    return out


def readme_block(m):
    fr, fa, st = frames.info(m)
    r = load_run(m)
    mp = frames.frame_map(fr)
    lines = ["<!-- F05 -->", "", "## Family F05: one core, forty machines", ""]
    lines.append(
        f"This machine is one of 40 holdouts with the same five states. In frame A all of them are "
        f"`{CORE}`: they differ in D1 (0LF or 1LF), in F0 and in the start state. "
        + (f"This one is the core itself with D1 = {d1(fa)}, F0 = {f0(fa)}, started in {st}."
           if fr == "A" else
           f"This one is the mirror image of `{fa}` with the states renamed "
           + ", ".join(f"{s}->{mp[s]}" for s in frames.STATES) + f" (frame {fr}), started in that table's state {st}.")
        + f" `lean/Family.lean` proves it (`step_img`, `halts_iff`: the machine halts from blank tape iff `{fa}` "
        f"halts from blank tape in state {st}).")
    lines += ["", "Shared by all 40 and proved in Lean on each machine's own frame-A table (`lean/Family.lean`, "
              f"written by `{SHARED}/py/gen_family_lean.py`):", "",
              "- `go_spec`: the visit rule for every depth (a clean visit to [b1, ..., bk] makes five visits to the "
              "list without b1);",
              "- `go_closed`, `visit_closed`: its closed form (b1-5, b2-18, b3-90, ..., bk+12·5^(k-2));",
              "- `visit_conserves` (new): a clean visit conserves, for the blocks after the first and before the "
              "last, the residue of block i modulo 18·5^(i-2) and the drift b(i+1) - 5·b(i);",
              "- `birth`, `fevent`, `fevent_reads_zero`: the birth of a block, and the harmless entry into F.", ""]
    if r:
        ctx = "; ".join(f"`{c['context']}` ({c['count']}x)" for c in r["f_contexts"])
        v = r.get("validated")
        lines.append(
            f"**Run (trusted).** The exact block-list map (`{SHARED}/py/f05_run.py`, `{r['simulator']}`) reaches "
            f"step {sci(r['steps'], md=True)} without a halt: {r['left_end_events']} returns to the left end, "
            f"{r['f_events']} entries into F, all reading 0, tape around the head {ctx}."
            + (f" Its F-events agree with the plain simulation on the first {v['direct_steps']} steps "
               f"({v['f_events']} F-events)." if v and v["match"] else "")
            + " Summary and the first 80 left-end block lists: `data/f05_run.json`.")
        d = r["drift"]
        lines += ["", "**Drifts (observed, at left-end events only).** Smallest |b(i+1) - 5·b(i)| after step 10^20: "
                  f"{d.get('smallest_after_1e20')}; after step 10^100: {d.get('smallest_after_1e100')}. Halting "
                  "would need a drift near 0 at the moment its block runs out (two exceptional events close "
                  "together); nothing proved excludes that, so the question stays open."]
    lines += ["", "The (D1, F0) variants and their machines (runs marked with the same letter had the same block "
              "list at their last left-end event, observed):", "", variant_table(m, md=True), "",
              "<!-- end F05 -->"]
    return "\n".join(lines)


# ------------------------------------------------------------------------------------------ the five other machines

def other_section(m, rel, obs):
    h = [
        "<p>The family plan groups this machine with the <b>nested block counter</b>: 40 holdouts that are one "
        f"five-state core <code>{CORE}</code> in different frames. This machine's table is <b>not</b> a renaming "
        "or mirror image of that core, so the family's Lean theorems (the visit rule, its closed form, the "
        "conserved residues and drifts) are not proved for it.</p>",
        f"<p>What ties it to the family is an observation about runs: compared with "
        f"<code>{link(rel, m)}</code>, {obs}. If that held for the whole run the two machines would write the same "
        "tapes, but their halting transitions are read in different situations, so even then one halting question "
        "would not settle the other without a further argument.</p>",
        "<p>The family's members and how far each has been run:</p>" + variant_table(m),
    ]
    return {"id": "f05", "eyebrow": "The family", "heading": "Next to the forty-machine core", "html": h}


def other_claims(m, rel, obs):
    return [{"level": "trusted", "tag": "F05", "title": "Grouped with the 40-machine block counter, by its tapes",
             "text": (f"The table is not a renaming or mirror image of the core <code>{CORE}</code> (all 720 "
                      f"renamings in both orientations, <code>frames.core_frames</code>). Compared with <code>{rel}</code>: {obs}. An observation, not a proof; the "
                      "family's Lean theorems do not cover this machine."),
             "where": f"<code>{SHARED}/py/frames.py</code> (<code>core_frames</code>), "
                      f"<code>{SHARED}/py/f05_records.py</code> (<code>OTHER</code>)"}]


def other_readme(m, rel, obs):
    o = html.unescape(obs.replace("<code>", "`").replace("</code>", "`").replace("<sup>", "^").replace("</sup>", ""))
    return "\n".join([
        "<!-- F05 -->", "", "## Family F05: next to the forty-machine core", "",
        f"The family plan groups this machine with the nested block counter, 40 holdouts that are the core `{CORE}` "
        "in different frames. This machine's table is not a renaming or mirror image of that core, so the family's "
        f"Lean theorems are not proved for it. Compared with [`{rel}`](../{rel}/README.md): {o}. That is an "
        "observation, and the two halting transitions are read in different situations, so one halting question "
        f"does not settle the other. The family's records are in [`{LEAD}`](../{LEAD}/README.md).", "",
        "<!-- end F05 -->"])


# ------------------------------------------------------------------------------------------------------ writing

def insert_claims(spec, new):
    cl = [c for c in spec["claims"] if c.get("tag") != "F05"]
    # after the three generated base claims (halting configurations, 10^4 kernel, 10^7 native)
    k = min(3, len(cl))
    spec["claims"] = cl[:k] + new + cl[k:]


def insert_section(spec, sec):
    ex = spec.setdefault("explainer", {})
    ss = [s for s in ex.get("sections", []) if s.get("id") != "f05"]
    ex["sections"] = [sec] + ss


def insert_readme(text, block):
    a, b = "<!-- F05 -->", "<!-- end F05 -->"
    if a in text:
        i, j = text.index(a), text.index(b) + len(b)
        return text[:i] + block + text[j:]
    for mark in ("\n## Pages\n", "\n## Check\n", "\n## Reproduce\n"):
        if mark in text:
            i = text.index(mark)
            return text[:i] + "\n" + block + "\n" + text[i:]
    return text.rstrip("\n") + "\n\n" + block + "\n"


CHECK = "python3 {s}/py/f05_run.py {m} 1e200          # the exact block-list map; writes data/f05_run.json"


def write(m, sec, cls, block, run):
    p = os.path.join(HOLD, m, "status.json")
    spec = json.load(open(p))
    insert_section(spec, sec)
    insert_claims(spec, cls)
    spec["asof"] = ASOF
    if run:
        line = CHECK.format(s=SHARED, m=m).replace("1e200", run["target_steps"])
        spec["check"] = [c for c in spec.get("check", []) if "f05_run.py" not in c] + [line]
        note = (f"<b>Family F05.</b> One of 40 holdouts on the same five-state core; the family's exact block-list "
                f"map runs this machine for {sci(run['steps'])} steps without a halt.")
        spec["verdict"] = [v for v in spec.get("verdict", []) if not v.startswith("<b>Family F05.</b>")] + [note]
    with open(p, "w") as f:
        json.dump(spec, f, indent=1, ensure_ascii=False)
        f.write("\n")
    q = os.path.join(HOLD, m, "README.md")
    text = open(q).read()
    with open(q, "w") as f:
        f.write(insert_readme(text, block))


def main(argv):
    fam = [r[0] for r in frames.FAMILY]
    oth = {r[0]: r for r in OTHER}
    for m in argv or fam + list(oth):
        if m in oth:
            assert frames.core_frames(m) == [], m
            _, rel, obs = oth[m]
            write(m, other_section(m, rel, obs), other_claims(m, rel, obs), other_readme(m, rel, obs), None)
        else:
            if load_run(m) is None:
                print("no data/f05_run.json yet:", m)
                continue
            write(m, section(m), claims(m), readme_block(m), load_run(m))
        print("wrote", m)


if __name__ == "__main__":
    main(sys.argv[1:])
