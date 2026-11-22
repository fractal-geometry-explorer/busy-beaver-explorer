"""Put the layer law into status.json (claims, verdict, the explainer's sections, with the widget of
py/layers_widget.html and the presets of py/layers_presets.json).  Run once after a change; then
python3 holdouts/build_pages.py MACHINE rebuilds the pages.
usage (from the repository root): python3 holdouts/1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA/py/layers_page.py"""
import json, os
HERE = os.path.dirname(os.path.abspath(__file__)); ST = os.path.join(HERE, '..', 'status.json')
d = json.load(open(ST))
pre = json.load(open(os.path.join(HERE, 'layers_presets.json')))
widget = open(os.path.join(HERE, 'layers_widget.html')).read().replace('__PRESETS__', json.dumps(pre, separators=(',', ':')))

LAYOUT = "<code>0<sup>∞</sup> 1 0 [N] A&gt; 0 [Z] (1 1 [Q] 0 1 [P] 1 0)* 1 1 [Q] 0 1 [R] 0<sup>∞</sup></code>"
d['verdict'] = [
    "<b>The question is open.</b> The engine is decoded and proved in Lean for every size: a base-3 counter N on the "
    "left gets 1 per event, and the right side is a binary counter Z followed by a <i>chain</i> of items, each a pair of "
    "binary words Q and P. When Z wraps it sends one unit into the chain; a unit adds 3 to an item's Q, every wrap of Q "
    "adds 3 to its P, and every wrap of P sends a unit into the next item. This one <b>layer law</b> covers every layout "
    "the run has shown (the plain cascade is one item, the late layout <code>Z2 d c a d c a X14 d C2 R13</code> is "
    "three) and is proved in Lean for every number of items and every width (<code>lean/Layers.lean</code>); all "
    "1,169,737 consecutive full events of a 3·10<sup>8</sup>-step run that stay in one layout follow it. No event can "
    "halt. A halt can only come at an <i>overflow of R</i>, a carry leaving the last word: 7 in that run, each "
    "rebuilding the chain (and sometimes taking digits of N). What an overflow hands on is the open part."]
d['summary'] = ("Two-word sweeper: a base-3 counter N and a chain of binary words; each event adds 1 to N and to Z, a wrap "
                "of Z sends a unit down the chain, multiplied by 3 at every separator (proved in Lean for every layout). "
                "Only the overflows of the last word R are open.")
d['explainer']['lede'] = ("Nobody knows whether it halts. Its engine is decoded and proved: a base-3 counter on the left "
                          "and a chain of binary words on the right tick together; each wrap of a word sends its carry to "
                          "the next word, multiplied by 3. The open question is what happens when the carry runs off the "
                          "end of the chain.")
claims = [c for c in d['claims'] if c['title'] not in ('The layered shapes of the later run', 'What the eras hand on, and the shapes between',
                                                      'The layer law, for every layout', 'The run follows the layer law', 'What an overflow of R hands on',
                                                      'Overflow after overflow, far beyond the run')]
i = next(j for j, c in enumerate(claims) if c['title'] == 'The cascade rule of the later layout, for every size') + 1
claims[i:i] = [
    {"level": "kernel", "title": "The layer law, for every layout",
     "text": "At an event the right side is " + LAYOUT + " with Z (digits <code>0010</code>, <code>1010</code>), each Q "
             "(<code>0001</code>, <code>0101</code>) and each P and R (<code>1000</code>, <code>1010</code>) binary, lowest digit "
             "first, of any width, Q and P possibly empty, any number of items. From one event to the next: N + 1, Z + 1; when "
             "Z wraps, one unit goes into the first item; a unit adds 3 to Q; each wrap of Q adds 3 to P; each wrap of P sends a "
             "unit into the next item, as long as no carry leaves R. Equivalently Z + 2<sup>|Z|</sup>/3 · (Q₁ + 2<sup>|Q₁|</sup>/3 "
             "· (P₁ + 2<sup>|P₁|</sup>/3 · (Q₂ + …))) grows by exactly 1 per event. Proved from 23 visit rows of blocks of 1, 2 "
             "and 4 cells, by induction over the digits of each word and the list of items; the cascade layout is one item.",
     "where": "<code>layer_event</code>, <code>layer_event_n0t0</code> … <code>layer_event_novk</code> (the 9 cases of N), <code>lean/Layers.lean</code>"},
    {"level": "trusted", "title": "The run follows the layer law",
     "text": "In the first 3·10<sup>8</sup> steps all 1,169,737 pairs of consecutive full events in a layered layout follow the "
             "law, computed with the functions of the Lean file, with no mismatch; 7 pairs are overflows of R; 4,122 full events "
             "(4,088 of them between steps 15,766 and 118,003) are in no layout. 12 layouts occur, from one item to four, the last "
             "<code>Z2 | (∅, ∅) (∅, P14) (Q2, R13)</code> from step 70,680,694 to the end of the run (436,712 events).",
     "where": "<code>holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/c/cascade_events.c</code> piped into <code>py/layers_check.py</code>"},
    {"level": "trusted", "title": "Overflow after overflow, far beyond the run",
     "text": "Between two overflows the layer law is applied in closed form (m events add m to N and Z, and the units sent "
             "down the chain add up with carries); each overflow event is run cell by cell on the machine. From step 118,003 "
             "this reproduces the 7 overflows of the run and then follows 1,500 overflows, to about 10<sup>874</sup> events, "
             "with no halt. At every overflow the next full event has N' = ⌊N / 3<sup>d</sup>⌋ + 1: the overflow eats d low "
             "base-3 digits of N (d = 1 never occurs; d counts 0: 482, 2: 446, 3: 302, 4: 155, 5: 68, 6: 33, 7: 9, 8: 4, 16: 1).",
     "where": "<code>py/overflow_jump.py</code> with <code>c/overflow_event.c</code>"},
    {"level": "open", "title": "What an overflow of R hands on",
     "text": "The exact law: which d and which new words follow from N's low digits and the chain. Seen so far: d = 0 merges "
             "two neighbouring words, d ≥ 2 shifts the word widths by one slot, and the last item alternates between "
             "(Q12, R0) and (Q2, R13). Then halting. No event of any layout can halt, since every rule is a run of the machine.",
     "where": ""},
]
d['claims'] = claims
chk = d['check']
line = ("gcc -O2 -o cascade_events holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/c/cascade_events.c && ./cascade_events "
        "1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA 0 300000000 0 | python3 holdouts/1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA/py/layers_check.py")
if line not in chk: chk.append(line)

ROWS = [("1,147 – 2,891", "Z1 | (Q6, R0)"), ("3,823 – 7,079", "Z1 | (Q7, R0)"), ("7,278 – 15,604", "Z2 | (∅, R9)"),
        ("118,003 – 322,617", "Z2 | (Q12, R0)"), ("322,900 – 664,016", "Z2 | (Q2, R13)"),
        ("666,019 – 1,200,511", "Z1 | (∅, ∅) (Q3, P2) (Q12, R0)"), ("1,201,439 – 3,303,831", "Z1 | (Q5, P2) (Q12, R0)"),
        ("3,304,127 – 8,321,787", "Z3 | (Q5, P2) (Q12, R0)"), ("8,322,224 – 18,198,332", "Z2 | (Q2, P6) (Q2, R13)"),
        ("18,199,027 – 38,655,981", "Z1 | (Q3, P1) (Q7, P2) (Q12, R0)"), ("38,659,480 – 70,678,024", "Z2 | (∅, ∅) (∅, P4) (∅, P8) (Q2, R13)"),
        ("70,680,694 – 299,999,430", "Z2 | (∅, ∅) (∅, P14) (Q2, R13)")]
EV = [38, 67, 114, 5462, 7284, 1076, 38868, 155478, 207300, 276400, 40948, 436712]
tab = "<table class=\"tbl\"><thead><tr><th>steps</th><th>layout (widths: Z | (Q, P) of each item)</th><th>full events</th></tr></thead><tbody>" + \
      "".join(f"<tr><td>{a}</td><td><code>{b}</code></td><td>{c:,}</td></tr>" for (a, b), c in zip(ROWS, EV)) + "</tbody></table>"
OV = [("322,617", "N 2,337 · Z 3 | (4095, 0)", "322,900", "N 87 · Z 0 | (3, 4096)"),
      ("664,016", "N 4,211 · Z 3 | (3, 8191)", "666,019", "N 18 · Z 0 | (0, 0) (5, 2) (12, 0)"),
      ("1,200,511", "N 13 · Z 1 | (0, 0) (0, 1) (4092, 0)", "1,201,439", "N 14 · Z 0 | (4, 0) (0, 0)"),
      ("3,303,831", "N 10,450 · Z 1 | (31, 3) (4095, 0)", "3,304,127", "N 1,162 · Z 2 | (0, 0) (0, 0)"),
      ("8,321,787", "N 71,346 · Z 7 | (30, 3) (4095, 0)", "8,322,224", "N 2,643 · Z 0 | (3, 2) (0, 4096)"),
      ("18,198,332", "N 124,649 · Z 3 | (3, 62) (3, 8191)", "18,199,027", "N 4,617 · Z 0 | (0, 1) (5, 0) (0, 0)"),
      ("70,678,024", "N 12,593 · Z 3 | (0, 0) (0, 15) (0, 242) (3, 8191)", "70,680,694", "N 12,594 · Z 0 | (0, 0) (0, 128) (0, 4096)")]
ovt = "<table class=\"tbl\"><thead><tr><th>step</th><th>before (values)</th><th>step</th><th>after</th></tr></thead><tbody>" + \
      "".join(f"<tr><td>{a}</td><td><code>{b}</code></td><td>{c}</td><td><code>{e}</code></td></tr>" for a, b, c, e in OV) + "</tbody></table>"

secs = [s for s in d['explainer']['sections'] if s['id'] not in ('layers', 'overflows')]
for s in secs:
    if s['id'] == 'eras':
        s['heading'] = 'A cascade, then a chain of words'
        s['html'] = [
            s['html'][0],
            "<p>The later run carries more words between Z and R, and they all obey one law. Read the right side as Z followed by a "
            "<b>chain of items</b>, each a pair of binary words Q and P (either may be empty), the last P being R:</p>"
            f"<p style=\"text-align:center\">{LAYOUT}</p>"
            "<p>The blocks <code>1 1</code>, <code>0 1</code> and <code>1 0</code> are separators, and each one the carry passes "
            "<b>multiplies it by 3</b>. When Z wraps it sends one <i>unit</i> into the first item. A unit is three increments of "
            "Q (the machine visits Q three times); every time Q wraps, the block <code>0 1</code> after it turns that carry into "
            "three increments of P; every time P wraps, the block <code>1 0</code> sends one unit into the next item. So the "
            "late layout of the run, with two empty items in front, adds 3·3·3·3 = 81 to its 14-digit word at every wrap of Z, "
            "which the run shows (6,400, 6,481, 6,562, … every four events).</p>"
            "<p>This is proved in Lean for every layout at once (<code>lean/Layers.lean</code>: 23 short visit rows, composed by "
            "induction over the digits of each word and over the list of items), and every one of the 1,169,737 consecutive "
            "pairs of full events of a 3·10<sup>8</sup>-step run that stay in a layout follows it. The layouts of the run:</p>",
            tab,
            "<p>Try it below: pick a layout of the run, step events, and let the page run the machine itself on the encoded tape "
            "to check that it leaves exactly the predicted words.</p>",
            widget]
i = next(j for j, s in enumerate(secs) if s['id'] == 'eras') + 1
secs.insert(i, {"id": "overflows", "eyebrow": "Where the law stops", "heading": "Overflows of R",
    "html": ["<p>The law stops only when a carry runs off the end of the chain, out of R. That is the only place a halt could "
             "come from, since every event that follows the law is a run of the machine that never reads the halting 1. In "
             "3·10<sup>8</sup> steps it happens 7 times, and each time the next full event has a new layout:</p>", ovt,
             "<p>Words merge (the last one turns <code>(0, 15) (0, 242)</code> into one 14-digit word, <code>128</code>), Q's "
             "digits move into a longer R, and five of the seven take 2 to 5 base-3 digits from N, mixing base 3 into base 2 as in "
             "the sibling with F0 = 0LB.</p>",
             "<p>Past the run, the law does the work: between two overflows m events can be added in one step (N + m, Z + m, "
             "and the units sent down the chain added with carries), and only the overflow event itself is run on the machine. "
             "That follows 1,500 overflows, to about 10<sup>874</sup> events, with no halt. Every one of them obeys one rule "
             "on the left: the overflow eats d low base-3 digits of N and the next event has N' = ⌊N / 3<sup>d</sup>⌋ + 1. "
             "d is never 1; most often it is 0 (two words merge) or 2 and more (the widths shift by one slot). Which d, and "
             "which new words, is what remains between the engine and a decision.</p>"]})
for s in secs:
    if s['id'] == 'open':
        s['html'] = ["<p>The engine is proved for every layout: N + 1 on the left, and on the right the chain law, a carry "
                     "multiplied by 3 at each separator. The halting question now sits entirely in the overflows of R. Open: (1) "
                     "what an overflow hands on (the new widths and values, and which digits of N it takes); (2) whether the "
                     "sequence of overflows can ever put A on the halting 1; (3) the same chain law for the five siblings, whose "
                     "X layout is its two-item case.</p>"]
d['explainer']['sections'] = secs
json.dump(d, open(ST, 'w'), indent=1, ensure_ascii=False); open(ST, 'a').write('\n')
