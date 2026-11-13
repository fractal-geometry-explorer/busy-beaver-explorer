"""Writes the hand-made parts of this machine's status.json (verdict, claims, explainer sections with the two
widgets) from fam.py and the data of frames.py.  The machine-specific facts live in fam.FAMILY; the text is shared
by the four machines of the family.

usage: python3 page_sections.py            (from this folder; rewrites ../status.json, keeps the generated
                                            'shape' section and the header fields)
"""
import json, os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fam import FAMILY, MERGE, DIG

M = os.path.basename(os.path.dirname(HERE))
F = FAMILY[M]
S, R, NEAR = F['S'], F['R'], F['near']
OTHERS = [m for m in FAMILY if m != M]


def md(t):
    import re
    return re.sub(r'`([^`]*)`', r'<code>\1</code>', t)


def fmt(n):
    return f'{n:,}'


def sci(x):
    e = len(str(int(x))) - 1
    m = x / 10 ** e
    return (f'{m:.1f}&middot;' if abs(m - 1) > 0.05 else '') + f'10<sup>{e}</sup>'


def data():
    out = os.path.join(HERE, 'frames.json')
    if not os.path.exists(out):
        subprocess.run([sys.executable, os.path.join(HERE, 'frames.py'), M, S, out, '30000', '12']
                       + [f'{a}:{b}' for a, b in F['windows']], check=True)
    return json.load(open(out))


COL = {'a': 'var(--kernel)', 'b': 'var(--native)', 'c': 'var(--computed)', 'd': 'var(--head)', 'e': 'var(--muted)',
       'z': 'var(--heur)', 'f': 'var(--fg2)', 'x': 'var(--open)'}


def chip(x, label=None):
    return (f'<span style="display:inline-block;min-width:1.6em;padding:1px 4px;border-radius:4px;color:#fff;'
            f'background:{COL[x]};font:12px var(--mono);text-align:center">{label or x}</span>')


def tape_svg():
    """The tape at a sample configuration, drawn cell by cell: left gap, three digits, gaps, the wall."""
    parts = [('00', 'p'), ('0001' * 3, 'W'), (DIG['c'], 'c'), ('0001' * 2, 'W'), (DIG['e'], 'e'), ('0001' * 2, 'W'),
             (DIG['a'], 'a'), ('0001' * 2, 'W'), ('001', 'f')]
    cells = []
    for w, k in parts:
        for ch in w:
            cells.append((ch, k))
    cw, y0 = 13, 28
    W = len(cells) * cw + 20
    o = [f'<svg viewBox="0 0 {W} 92" role="img" aria-label="a sample configuration: left gap, digits c, e, a, '
         f'gaps of 0001, the wall 001" style="width:100%;max-width:{W}px;height:auto;font:10px var(--mono)">']
    x = 10
    for i, (ch, k) in enumerate(cells):
        fill = 'var(--ink)' if ch == '1' else 'var(--cell0)'
        stroke = COL.get(k, 'var(--line-strong)') if k not in 'Wp' else 'var(--line-strong)'
        o.append(f'<rect x="{x}" y="{y0}" width="{cw - 1}" height="{cw - 1}" fill="{fill}" stroke="{stroke}" '
                 f'stroke-width="{2 if k not in "Wp" else 1}"/>')
        if i == 0:
            o.append(f'<text x="{x + 6}" y="{y0 - 6}" text-anchor="middle" fill="var(--head)">{S}&#9662;</text>')
        x += cw
    # labels under the groups
    x = 10
    for w, k in parts:
        n = len(w)
        mid = x + n * cw / 2
        lab = {'p': '', 'W': f'W<tspan dy="-4" font-size="8">{len(w) // 4}</tspan>', 'f': 'wall'}.get(k, k)
        col = COL.get(k, 'var(--muted)') if k not in 'Wp' else 'var(--muted)'
        o.append(f'<text x="{mid}" y="{y0 + cw + 16}" text-anchor="middle" fill="{col}">{lab}</text>')
        if k == 'W':
            o.append(f'<path d="M{x + 1},{y0 + cw + 3} h{n * cw - 3}" stroke="var(--line-strong)"/>')
        x += n * cw
    o.append(f'<text x="10" y="{y0 + cw + 36}" fill="var(--muted)">blank tape to the left; the head (state {S}) '
             f'on the leftmost cell; blank tape after the wall</text></svg>')
    return ''.join(o)


def rule_table():
    rows = [('a', '1', 'b', '2', 'one W fewer after it'), ('b', '2', 'c', '3', '&mdash;'), ('c', '3', 'd', '4', '&mdash;'),
            ('d', '4', 'e', '0', 'carry: the head goes on to the next digit'),
            ('e', '0', 'a', '1', 'one W moves from the gap after it to the gap before it')]
    o = ['<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>digit</th><th>cells</th><th>value</th>'
         '<th>after the visit</th><th>gaps</th></tr></thead><tbody>']
    for x, v, y, w, g in rows:
        o.append(f'<tr><td>{chip(x)}</td><td><code>{DIG[x]}</code></td><td>{v}</td><td>{chip(y)} = {w}</td>'
                 f'<td>{g}</td></tr>')
    o.append('</tbody></table></div>')
    return ''.join(o)


STEPPER_JS = r'''
<div id="ctr-box" style="border:1px solid var(--line);border-radius:8px;padding:10px;background:var(--surface)">
 <div style="display:flex;flex-wrap:wrap;gap:6px;align-items:center;margin-bottom:8px">
  <select id="ctr-scene" style="font:13px var(--body)"></select>
  <button id="ctr-prev" type="button">&#9664;</button><button id="ctr-play" type="button">play</button>
  <button id="ctr-next" type="button">&#9654;</button>
  <span id="ctr-info" style="font:12px var(--mono);color:var(--fg2)"></span>
 </div>
 <div id="ctr-row" style="display:flex;flex-wrap:wrap;gap:3px;align-items:center;min-height:2.2em"></div>
 <p id="ctr-note" style="font-size:13px;color:var(--fg2);margin:8px 0 0"></p>
</div>
<script>
(function () {
  var SC = __SCENES__;
  var COL = {a: "--kernel", b: "--native", c: "--computed", d: "--head", e: "--muted", z: "--heur", f: "--fg2"};
  var VAL = {a: 1, b: 2, c: 3, d: 4, e: 0};
  var sel = document.getElementById("ctr-scene"), row = document.getElementById("ctr-row");
  var info = document.getElementById("ctr-info"), note = document.getElementById("ctr-note");
  var s = 0, i = 0, timer = null;
  SC.forEach(function (sc, k) { var o = document.createElement("option"); o.value = k; o.textContent = sc.title; sel.appendChild(o); });
  function chip(text, bg, fg, border) {
    var e = document.createElement("span");
    e.style.cssText = "display:inline-block;padding:2px 5px;border-radius:4px;font:12px var(--mono);" +
      "background:" + bg + ";color:" + fg + ";" + (border ? "border:1px solid " + border : "");
    e.innerHTML = text; return e;
  }
  function counter(t) {
    var ds = [];
    t.forEach(function (x) { if (typeof x === "string" && VAL[x] !== undefined) ds.push(VAL[x]); else if (x === "z") ds.push(0); });
    return ds.reverse().join("");
  }
  function draw() {
    var f = SC[s].frames[i], t = f[2];
    row.innerHTML = "";
    t.forEach(function (x, k) {
      if (typeof x === "number") {
        var w = Math.max(18, Math.min(140, 14 * Math.log(1 + x)));
        var e = chip("W<sup>" + x + "</sup>", "var(--sunk)", "var(--fg2)", "var(--line)");
        e.style.minWidth = w + "px"; e.style.textAlign = "center"; row.appendChild(e);
      } else if (k === 0) {
        row.appendChild(chip("__S__&#9656;" + (x === "[00]" ? "" : " " + x.replace(/[\[\]]/g, "")), "transparent", "var(--head)", "var(--head)"));
      } else if (x === "f" && k === t.length - 1) {
        row.appendChild(chip("001&#9612;", "transparent", "var(--fg2)", "var(--line-strong)"));
      } else if (COL[x]) {
        row.appendChild(chip(x + (VAL[x] !== undefined ? "<sub>" + VAL[x] + "</sub>" : ""), "var(" + COL[x] + ")", "#fff"));
      } else {
        row.appendChild(chip(x.replace(/[\[\]]/g, ""), "transparent", "var(--open)", "var(--open)"));
      }
    });
    info.textContent = "visit " + f[0].toLocaleString() + " · step " + f[1].toLocaleString() +
      " · digits read right to left: " + counter(t);
    note.textContent = SC[s].note;
  }
  function stop() { if (timer) { clearInterval(timer); timer = null; document.getElementById("ctr-play").textContent = "play"; } }
  sel.onchange = function () { stop(); s = +sel.value; i = 0; draw(); };
  document.getElementById("ctr-prev").onclick = function () { stop(); i = Math.max(0, i - 1); draw(); };
  document.getElementById("ctr-next").onclick = function () { stop(); i = Math.min(SC[s].frames.length - 1, i + 1); draw(); };
  document.getElementById("ctr-play").onclick = function () {
    if (timer) { stop(); return; }
    this.textContent = "pause";
    timer = setInterval(function () { if (i >= SC[s].frames.length - 1) { stop(); return; } i++; draw(); }, 450);
  };
  draw();
})();
</script>'''

TRACKS_JS = r'''
<div style="border:1px solid var(--line);border-radius:8px;padding:8px;background:var(--surface)">
<canvas id="trk-cv" style="width:100%;height:440px;display:block" aria-label="positions of the digits, visit by visit"></canvas>
<div id="trk-leg" style="font:12px var(--mono);color:var(--fg2);margin-top:6px"></div>
</div>
<script>
(function () {
  var T = __TRACKS__;
  var COL = {a: "--kernel", b: "--native", c: "--computed", d: "--head", e: "--muted", z: "--heur", f: "--fg2", x: "--open"};
  var cv = document.getElementById("trk-cv");
  function css(v) { return getComputedStyle(document.documentElement).getPropertyValue(v).trim() || "#888"; }
  function draw() {
    var dpr = window.devicePixelRatio || 1, W = cv.clientWidth, H = cv.clientHeight;
    cv.width = W * dpr; cv.height = H * dpr;
    var g = cv.getContext("2d"); g.scale(dpr, dpr); g.clearRect(0, 0, W, H);
    var maxw = 0; T.rows.forEach(function (r) { if (r[1] > maxw) maxw = r[1]; });
    var pl = 8, pr = 8, pt = 18, pb = 22, n = T.rows.length;
    function X(p) { return W - pr - p / maxw * (W - pl - pr); }
    function Y(k) { return pt + k / (n - 1) * (H - pt - pb); }
    g.font = "11px " + css("--mono");
    g.fillStyle = css("--muted");
    g.fillText("visit 0", pl, pt - 6);
    g.fillText("visit " + T.rows[n - 1][0].toLocaleString(), pl, H - 6);
    g.textAlign = "right"; g.fillText("right end of the tape →", W - pr, pt - 6);
    var cols = {}; for (var c in COL) cols[c] = css(COL[c]);
    var ink = css("--ink");
    T.rows.forEach(function (r, k) {
      var y = Y(k);
      g.fillStyle = ink; g.fillRect(X(r[1]) - 1, y, 2, 1.6);
      if (!r[2]) return;
      r[2].split(",").forEach(function (q) {
        var p = +q.slice(0, -1), t = q.slice(-1);
        g.fillStyle = cols[t] || cols.x; g.fillRect(X(p) - 1, y, 2.2, 1.6);
      });
    });
  }
  var leg = document.getElementById("trk-leg");
  leg.innerHTML = "<span style='color:var(--ink)'>&#9632; left end</span> &nbsp;" +
    [["a", "a = 1"], ["b", "b = 2"], ["c", "c = 3"], ["d", "d = 4"], ["e", "e = 0"], ["z", "z (empty digit)"], ["x", "other words (collisions)"]]
      .map(function (p) { return "<span style='color:var(" + COL[p[0]] + ")'>&#9632; " + p[1] + "</span>"; }).join(" &nbsp;");
  draw();
  var to; window.addEventListener("resize", function () { clearTimeout(to); to = setTimeout(draw, 150); });
  if (window.matchMedia) window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", draw);
})();
</script>'''


def sections(d):
    near_desc = F['near_desc']
    runs = F['runs']
    others = ', '.join(f'<a href="../{m}/explainer.html"><code>{m}</code></a>' for m in OTHERS)
    merge_table = ''.join(
        f'<tr><td><code>{m}</code>{" (this one)" if m == M else ""}</td><td>{md(MERGE[m][1])}</td></tr>' for m in FAMILY)
    scenes = []
    for (v0, nf), title, note, fr in zip(F['windows'], F['window_titles'], F['window_notes'], d['frames']):
        scenes.append({'title': title, 'note': note, 'frames': fr})
    stepper = STEPPER_JS.replace('__SCENES__', json.dumps(scenes, separators=(',', ':'))).replace('__S__', S)
    rows = []
    for v, st, w, row in d['tracks']:
        rows.append([v, w, ','.join(f'{p}{t}' for p, t in row)])
    tracks = TRACKS_JS.replace('__TRACKS__', json.dumps({'rows': rows}, separators=(',', ':')))
    G = F['costs']
    sec = []
    sec.append({'id': 'tape', 'eyebrow': 'Macro structure', 'heading': 'What the tape is made of', 'html': [
        f'<p>Stop the machine each time its head stands on the leftmost cell of the tape in state <b>{S}</b> (a '
        f'<em>sample configuration</em>). The tape then always reads the same way: a long periodic background of the '
        f'four-cell word <code>W = 0001</code>, interrupted by a few short <em>defects</em>, and closed on the right by a '
        f'fixed wall <code>001</code> that hardly ever moves. The left end grows by three cells per sample.</p>',
        tape_svg(),
        f'<p>Almost every defect is one of five words, which we call <em>digits</em> and give values:</p>',
        rule_table(),
        f'<p>So the tape is <code>0 0 W<sup>g<sub>0</sub></sup> X<sub>1</sub> W<sup>g<sub>1</sub></sup> X<sub>2</sub> '
        f'&hellip; X<sub>k</sub> W<sup>g<sub>k</sub></sup> 0 0 1</code>: a <em>left gap</em> of g<sub>0</sub> copies of W, '
        f'then digits, each followed by its own gap. A sixth defect, the single extra <code>0</code> (written '
        f'{chip("z")}), is an empty digit; it appears when the counter overflows (below).</p>']})
    sec.append({'id': 'visit', 'eyebrow': 'Macro structure', 'heading': 'One visit is one increment', 'html': [
        f'<p>Between two sample configurations the head makes one <em>visit</em>: it runs right through the left gap '
        f'(turning each <code>0001</code> into <code>1010</code> as it goes, {G["W"]} steps per W there and back), reaches the first '
        f'digit, and acts on it. A {chip("d")} (value 4) becomes {chip("e")} (value 0) and the head runs on to the next '
        f'digit: a <em>carry</em>. Any other digit takes one step up (a&rarr;b&rarr;c&rarr;d, e&rarr;a) and the head turns '
        f'back, restoring the background on its way to the left end, where it adds three cells. Read with the first '
        f'digit as the least significant, the digits are a <b>base-5 counter, incremented once per visit</b>.</p>',
        f'<p>The increment also moves the digits. <code>a&rarr;b</code> and <code>e&rarr;a</code> each take one W '
        f'from the gap after the digit; <code>e&rarr;a</code> gives it to the gap before; every visit adds a W to the left gap. '
        f'In cells, a digit moves 9 cells to the right per 5 increments, while the left end moves 3 cells left per '
        f'visit. Digit i is incremented once every 5<sup>i</sup> visits, so the lowest digit runs right at about 1.8 '
        f'cells per visit, the next at a fifth of that, and the high digits barely move: <b>every digit slowly '
        f'catches up with the next one.</b></p>',
        '<p>Step through real stretches of the run (computed by the exact visit simulator; the counter is shown with '
        'the most significant digit first):</p>',
        stepper,
        f'<p>Exactly: if the digits after the left gap are d&hellip;d X with X &ne; d and at least one W after X, the visit '
        f'takes {G["g0"]}&middot;g<sub>0</sub> + {G["visit"]} + &sum;<sub>passed d</sub>({G["d"]}&middot;g<sub>i</sub> + '
        f'{G["dk"]}) + {G["bounce"]} steps and gives the counter plus one with the gaps moved as above. Lean proves this '
        f'for every list of digits and gaps and every tape beyond (<code>visit</code> in <code>lean/Counter.lean</code>); '
        f'in the run it describes {F["plain"]} of all visits.</p>']})
    sec.append({'id': 'drift', 'eyebrow': 'Emergent behaviour', 'heading': 'Digits are born, drift and collide', 'html': [
        '<p>Every twelfth sample configuration of the first 30,000 visits, one row each, time going down; each defect is a '
        'dot at its distance from the right end of the tape. The black line is the left end, moving left; a line that '
        'starts on it is a digit born there.</p>',
        tracks,
        '<p>Three things happen, and only three:</p>',
        '<ul><li><b>Drift.</b> The lowest digit starts at the left end and runs right at about 1.8 cells per visit; '
        'higher digits crawl, the highest stand almost still near the wall.</li>'
        '<li><b>Overflow.</b> When every digit is d (the counter reads 44&hellip;4), the carry runs into the wall. All the '
        'd become empty digits z, the wall moves a few cells to the right, and a new digit is born at the left end. The '
        'counter gains a digit.</li>'
        '<li><b>Collision.</b> When the lowest digit reaches the next one (the gap between them runs out), the two '
        'stand side by side and the plain rule no longer applies. The gap runs out on an a&rarr;b or e&rarr;a step, so '
        'a collision starts as a or b next to any of the five digits. For a few increments the pair forms compound '
        'words; then it fuses into a single digit (the counter loses a digit and its value jumps), or it leaves a '
        'phase defect <code>001</code>, and the next visit gives birth to a new lowest digit at the left end.</li></ul>',
        f'<p>Overflows and collisions are rare: in the first 10<sup>13</sup> steps they touch {F["nonplain13"]} of '
        f'{F["visits13"]} visits. Between them the machine is a clean base-5 counter whose digits spread across a tape '
        f'of width about the square root of the step count. That is the fixed/sqrt growth of the triage.</p>']})
    sec.append({'id': 'halt', 'eyebrow': 'Where it could halt', 'heading': 'A near miss inside some collisions', 'html': [
        f'<p>The machine halts only in state <b>{F["halt_state"]}</b> reading a 1. It gets there only from state '
        f'<b>{NEAR}</b> reading <code>0 1</code>: {near_desc}. So it halts exactly when the head, in state {NEAR}, '
        f'finds <code>0 1 1</code>. In the background and in every plain visit, {NEAR} always finds <code>0 0</code>.</p>',
        f'<p><code>{NEAR}&gt;0 1</code> does happen, but only inside a few kinds of collision (for example when two e '
        f'meet), and there the next cell has always been a 0. In the first 10<sup>15</sup> steps it happened '
        f'{runs["near15"]} times, each time followed by <code>0</code>. Configurations built by hand with crowded '
        f'digits (several collisions at once, or compound words next to each other) do reach <code>0 1 1</code> and '
        f'halt: {F["crowd"]} random tapes with gaps of 0 to 3 halted within 3&middot;10<sup>6</sup> steps. So the question is whether the counter ever crowds its digits '
        f'that badly. That depends on the exact gaps at the moment of each collision, which depend on the whole '
        f'history of the counter.</p>']})
    sec.append({'id': 'family', 'eyebrow': 'Four machines, one counter', 'heading': 'Where the four machines part ways', 'html': [
        f'<p>This machine and three others, {others}, run exactly the same counter: the same tape at every sample '
        f'configuration, up to renaming the states. 1RB0LD_0LB1RC_0RD---_1RE0RF_1LF0RA_0LA0LF steps over each '
        f'<code>0 0</code> in four steps where the other three take two (so 12 steps per W per visit against 10; '
        f'{G["W"]} here), with the same result; the three others differ from each other only in what follows the near '
        f'miss. So the four runs first part ways at the first <code>0 1 0</code> (step 49,361 for the first machine, '
        f'49,247 for the others), and again at every later one. The commonest case is two e side by side:</p>',
        '<div style="overflow-x:auto"><table class="tbl"><thead><tr><th>machine</th><th>two e side by side become</th>'
        f'</tr></thead><tbody>{merge_table}</tbody></table></div>',
        '<p>After that the four runs are different counters with the same rules, and they collide differently. Each '
        'one is open for the same reason.</p>']})
    sec.append({'id': 'proved', 'eyebrow': 'What is proved', 'heading': 'What is proved, and what is left', 'html': [
        '<ul>'
        '<li><b>Lean, kernel:</b> the nine piece rules of a visit for all counts (<code>lean/Pieces.lean</code>); '
        '<code>visit</code>: one visit is one base-5 increment with the gap moves above, for every configuration where '
        'the increment is defined (<code>lean/Counter.lean</code>); the merge of two adjacent e '
        '(<code>lean/Merge.lean</code>).</li>'
        f'<li><b>Lean, native_decide:</b> the run from blank tape reaches a sample configuration of standard digits after '
        f'{fmt(F["reach"][0])} steps, and the counter rule alone then carries it {F["counted"]} more visits '
        f'(<code>reach</code>, <code>counted</code> in <code>lean/Reach.lean</code>).</li>'
        f'<li><b>Computed:</b> an exact visit-level simulator (<code>py/vsim.py</code>, identical to the direct '
        f'simulator on every sample configuration of the first 3&middot;10<sup>7</sup> steps) finds no halt in the first '
        f'{runs["far_html"]} steps ({runs["far_visits"]} visits).</li>'
        '<li><b>Open:</b> the collisions. A proof of non-halting would need to show that the counter never brings its '
        'digits into a crowded collision that reads <code>0 1 1</code>, which needs control of all the gaps at once.</li></ul>']})
    return sec


def main():
    p = os.path.join(HERE, '..', 'status.json')
    spec = json.load(open(p))
    d = data()
    runs = F['runs']
    spec['generated'] = False
    spec['group'] = 'G05'
    spec['family'] = 'base-5 counter with drifting, colliding digits'
    spec['summary'] = ('A base-5 counter whose digits are defects in a 0001 background; each sweep adds one; the digits '
                       'drift right and collide, and a near miss of the halt occurs inside some collisions.')
    spec['decision'] = 'open'
    spec['verdict'] = [
        f'<b>The question is open.</b> The machine is a base-5 counter, incremented once per sweep, whose digits drift '
        f'and collide; Lean proves the counting rule for all configurations, and an exact simulator of that structure '
        f'finds no halt in the first {runs["far_html"]} steps. Halting needs a crowded collision that the run has '
        f'never produced, and nothing proves it never will.']
    claims = [c for c in spec['claims'] if c['level'] in ('kernel', 'native') and 'Blank' in c.get('where', '')]
    claims += [
        {'level': 'kernel', 'title': 'The piece rules of a visit',
         'text': 'Nine rules, each for all counts and all surrounding tape: the crossing of the left gap, the carry over a d, '
                 'the turn at a, b, c or e, the return over a gap and over a passed d, and the growth at the left end.',
         'where': '<code>start</code>, <code>carry</code>, <code>bounce_a</code> &hellip; <code>left_end</code>, '
                  '<code>lean/Pieces.lean</code>'},
        {'level': 'kernel', 'title': 'One visit is one base-5 increment',
         'text': f'From a sample configuration <code>0 0 W^g X&#8321; W^g&#8321; &hellip; X&#8342; W^g&#8342; T</code> '
                 f'with digits a, b, c, d, e (values 1, 2, 3, 4, 0), whenever the increment <code>bump</code> is '
                 f'defined (the carry stops at a digit with a nonempty gap after it), the machine reaches the sample '
                 f'configuration of the incremented counter in exactly {F["costs"]["g0"]}g + {F["costs"]["visit"]} + '
                 f'<code>cost</code> steps; iterated in <code>run_sound</code>.',
         'where': '<code>visit</code>, <code>run_sound</code>, <code>lean/Counter.lean</code>'},
        {'level': 'kernel', 'title': 'The merge of two adjacent e',
         'text': 'The visit that meets two e side by side, the place where the four machines of the family differ: '
                 + md(MERGE[M][1]),
         'where': '<code>merge_ee</code>, <code>lean/Merge.lean</code>'},
        {'level': 'native', 'title': 'From blank tape into the counter',
         'text': f'After {fmt(F["reach"][0])} steps the run is at a sample configuration made of standard digits, and the '
                 f'counter rule alone carries it through the next {F["counted"]} visits.',
         'where': '<code>reach</code>, <code>counted</code>, <code>lean/Reach.lean</code>'},
        {'level': 'trusted', 'title': f'No halt in the first {runs["far_html"]} steps',
         'text': f'The visit-level simulator <code>py/vsim.py</code> (runs each visit on a copy with long gaps cut short and '
                 f'puts them back; identical to the direct simulator on all sample configurations of the first '
                 f'3&middot;10<sup>7</sup> steps) runs {runs["far_html"]} steps, {runs["far_visits"]} visits, without a '
                 f'halt. The near miss <code>{NEAR}&gt;0 1 0</code> occurs {runs["near15"]} times in the first '
                 f'10<sup>15</sup> steps.',
         'where': '<code>py/vsim.py</code>'},
        {'level': 'trusted', 'title': 'No halt in the first 10<sup>9</sup> steps',
         'text': 'The C simulator <code>tools/c/triage.c</code> runs 10<sup>9</sup> steps without a halt.',
         'where': '<code>holdouts/triage.json</code>'},
        {'level': 'heuristic', 'title': 'Collisions are where it could halt',
         'text': f'{F["plain"]} of the visits are plain increments. The others are overflows (all digits d) and '
                 f'collisions of a digit with the next. Hand-made tapes with crowded collisions reach '
                 f'<code>{NEAR}&gt;0 1 1</code> and halt; the run has met only isolated collisions so far.',
         'where': '<code>py/census.py</code>'},
        {'level': 'open', 'title': 'Does it halt from blank tape?',
         'text': 'Not known. It would take control of the gaps at every collision of the counter, forever.', 'where': ''},
    ]
    spec['claims'] = claims
    ex = spec['explainer']
    ex['lede'] = (f'A six-state machine that counts in base 5. Its digits are little defects in a periodic tape; each '
                  f'sweep of the head adds one to the number; the digits drift across the tape, overflow, and now and '
                  f'then crash into each other. Nobody knows whether one of those crashes will stop it. No halt in '
                  f'the first {runs["far_html"]} steps.')
    ex['facts'] = [
        {'level': 'kernel', 'value': 'base-5 counter', 'text': 'One sweep = one increment, proved for all configurations.'},
        {'level': 'trusted', 'value': runs['far_html'] + ' steps', 'text': 'No halt in the exact visit simulator.'},
        {'level': 'open', 'value': 'collisions', 'text': 'The only place a halt can come from.'},
    ]
    shape = [s for s in ex['sections'] if s['id'] == 'shape']
    ex['sections'] = shape + sections(d)
    spec['check'] = [
        '. /etc/profile.d/lean.sh      # after scripts/setup-lean.sh',
        f'holdouts/{M}/lean/check.sh',
        f'cd holdouts/{M}/py && python3 vsim.py {M} {S} 1e15 {NEAR}     # about 3 minutes',
    ]
    json.dump(spec, open(p, 'w'), indent=1, ensure_ascii=False)
    open(p, 'a').write('\n')


if __name__ == '__main__':
    main()
