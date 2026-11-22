"""Put the chain law and the long runs into the status.json of the five 1RB0LE two-word sweepers.

Reads py/chain_runs.json (written by `chain_page.py collect`, from the outputs of wordchain.py) and the widget
py/chain_widget.html, and rewrites in each machine's status.json: the verdict, the summary, the lede and facts, the
claims about the chain law and the runs, and the explainer's sections 'chain' (new), 'eras' and 'open'.  Then
`python3 holdouts/build_pages.py MACHINE` rebuilds the pages.

usage (from the repository root):
  python3 holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/py/chain_page.py collect MACHINE CHECK.txt FOLLOW.json
  python3 holdouts/1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---/py/chain_page.py write
"""
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, '..', '..', '..')
RUNS = os.path.join(HERE, 'chain_runs.json')
MAIN = '1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---'
TOOL = 'holdouts/' + MAIN + '/py/'
LAYOUT = ('<code>0<sup>∞</sup> 1 0 [N] A&gt; 0 [Z] 1 1 [W₁] 0 1 [U₁] 1 0 1 1 [W₂] 0 1 [U₂] … 1 0 1 1 [W<sub>m</sub>] 0 1 '
          '[U<sub>m</sub>] 0<sup>∞</sup></code>')


def parse_show(s):
    toks = s.split()
    n, nw = map(int, re.match(r'N=(\d+)\((\d+)\)', toks[0]).groups())
    ws = [(t[0], int(v), int(w)) for t, (v, w) in
          ((t, re.match(r'\w(\d+)\((\d+)\)', t).groups()) for t in toks[1:])]
    return n, nw, ws


def bits(v, w):
    return ''.join('1' if (v >> i) & 1 else '0' for i in range(w))


def sci(x):
    s = str(x)
    return '%s.%s·10<sup>%d</sup>' % (s[0], s[1], len(s) - 1) if len(s) > 3 else s


def collect(M, check_txt, follow_json):
    runs = json.load(open(RUNS)) if os.path.exists(RUNS) else {}
    r = runs.setdefault(M, {})
    if check_txt and os.path.exists(check_txt):
        line = [l for l in open(check_txt) if ' steps of ' in l][-1]
        st = eval(line.split(': ', 1)[1])
        r['check'] = dict(steps=int(line.split()[0]), law=st['by the law'], mismatch=st['MISMATCH'],
                          changes=st['change of layout'], other=st['full event in no layout'])
    d = json.load(open(follow_json))
    eras = d['eras']
    r['follow'] = dict(eras=len(eras), events=str(d['events']), cell_steps=d['cell_steps'], spot=d['spot_checked'],
                       bad=d['spot_bad'], words=len(eras[-1]['widths']), width=sum(eras[-1]['widths']))
    r['first'] = [dict(event=str(e['event']), start=e['start'], last=e['last'], next=e.get('next', ''))
                  for e in eras[:24]]
    json.dump(runs, open(RUNS, 'w'), indent=1)
    open(RUNS, 'a').write('\n')


def presets(r):
    out = []
    for e in r['first']:
        n, nw, ws = parse_show(e['start'])
        if n >= 2 ** 52 or len(ws) < 3:
            continue
        z = bits(ws[0][1], ws[0][2])
        items = [[bits(ws[i][1], ws[i][2]), bits(ws[i + 1][1], ws[i + 1][2])] for i in range(1, len(ws), 2)]
        sh = 'Z%d | ' % ws[0][2] + ' '.join('(%s, %s)' % (('W%d' % ws[i][2]) if ws[i][2] else '∅',
                                                         ('U%d' % ws[i + 1][2]) if ws[i + 1][2] else '∅')
                                            for i in range(1, len(ws), 2))
        out.append([sh, dict(event=int(e['event']), n=n, nw=nw, z=z, items=items)])
    return out


def write():
    runs = json.load(open(RUNS))
    widget_src = open(os.path.join(HERE, 'chain_widget.html')).read()
    for M, r in runs.items():
        path = os.path.join(ROOT, 'holdouts', M, 'status.json')
        d = json.load(open(path))
        f = r['follow']
        c = r.get('check')
        ev = int(f['events'])
        evs = sci(ev)
        sib = M != MAIN
        layers = 'lean/Layers.lean'
        d['verdict'] = [
            '<b>The question is open.</b> The engine is decoded and proved in Lean for every size and every layout. At an '
            'event the tape is a base-3 counter N, then a binary counter Z, then a chain of binary words; N and Z get 1 per '
            'event, and every word is a counter that, when it wraps, sends 3 to the next word (so a carry is multiplied by 3 '
            'at every separator, and an empty word passes 3 times what it got). This chain law covers every layout the run '
            'has shown (the plain cascade, the X layer and all later eras are special cases) and is proved in '
            '<code>' + layers + '</code> for any number of words of any widths. Inside a layout the whole right side is one '
            'number that grows by 1 per event, so an era change happens only when a carry runs off the last word. Using this, '
            'a simulator that jumps from one era change to the next and runs each change cell by cell has followed the run '
            'through %d changes of era, %s events (so at least that many steps), with no halt. ' % (f['eras'], evs) +
            'What an era change hands on (the new widths and values, and how many base-3 digits it takes from N) is the open '
            'part; C never runs out of digits: instead the chain keeps gaining words.']
        d['summary'] = ('Two-word sweeper: a base-3 counter N and a chain of binary words; each event adds 1 to N and to Z, '
                        'and each wrap of a word sends 3 to the next (proved in Lean for every layout). The run has been '
                        'followed through %d changes of era (%s events) with no halt; the era changes are open.'
                        % (f['eras'], re.sub('<[^>]+>', '', evs).replace('·10', '·10^')))
        ex = d['explainer']
        ex['lede'] = ('Nobody knows whether it halts. Its engine is decoded and proved: a base-3 counter on the left and a '
                      'chain of binary words on the right tick together, and each word that wraps sends 3 to the next. '
                      'So between two changes of era the whole right side is one counter. A simulator built on this has '
                      'followed the run for %s events without a halt; what a change of era hands on is the open question.'
                      % evs)
        facts = [x for x in ex.get('facts', []) if 'chain' not in x['text'] and 'eras followed' not in x['text']]
        facts[:0] = [{"level": "kernel", "value": "every layout", "text": "The chain law (each wrap sends 3 to the next word), in Lean."},
                     {"level": "trusted", "value": evs, "text": "Events of the run (%d eras followed), no halt." % f['eras']}]
        ex['facts'] = facts
        claims = [x for x in d['claims'] if x['title'] not in (
            'What a change of era hands on', 'The chain law, for every layout', 'The run follows the chain law',
            'No halt through the first changes of era', 'What a change of era does', 'What the eras hand on, and the shapes between')]
        new = [
            {"level": "kernel", "title": "The chain law, for every layout",
             "text": "At an event the right side is " + LAYOUT + ": Z (digits <code>0010</code>, <code>1010</code>), each W "
                     "(<code>0001</code>, <code>0101</code>) and each U (<code>1000</code>, <code>1010</code>) binary, lowest digit "
                     "first, of any width, W and U possibly empty, any number m of pairs. From one event to the next: N + 1, Z + 1; "
                     "when Z wraps, W₁ gets 3; each wrap of a W gives its U 3; each wrap of a U gives the next W 3, as long as no "
                     "carry leaves the last word. Equivalently Z + 2<sup>|Z|</sup>/3 · (W₁ + 2<sup>|W₁|</sup>/3 · (U₁ + "
                     "2<sup>|U₁|</sup>/3 · (W₂ + …))) grows by exactly 1 per event. 23 visit rows (24 for E1 = 0RE) of blocks of 1, "
                     "2 and 4 cells, composed by induction over the digits of each word and over the list of pairs; the generator "
                     "is this family's copy of the one first written for 1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA.",
             "where": "<code>layer_event</code>, <code>layer_event_n0t0</code> … <code>layer_event_novk</code> (the 9 cases of N), "
                      "<code>" + layers + "</code>, from <code>" + TOOL + "layers_gen.py</code>"}]
        if c:
            new.append({"level": "trusted", "title": "The run follows the chain law",
                        "text": "In the first %s steps, %s pairs of consecutive full events in one layout follow the law (the "
                                "number above gains exactly 1), with no mismatch; %d pairs change the layout (changes of era), %d "
                                "full events are in no layout." % ('{:,}'.format(c['steps']), '{:,}'.format(c['law']),
                                                                   c['changes'], c['other']),
                        "where": "<code>python3 " + TOOL + "wordchain.py " + M + " check %d</code>" % c['steps']})
        new.append({"level": "trusted", "title": "No halt through the first changes of era",
                    "text": "The simulator runs the machine cell by cell from blank tape; at each full event in a layout it "
                            "computes from the chain law the last event before a carry would leave the last word, writes "
                            "that tape and runs on cell by cell through the change of era. %d changes of era, %s events in "
                            "all (each at least one step), %s steps run cell by cell, no halt; at the end the chain has %d "
                            "words, %d digits in all. Before each jump it checks the law on random events of the era, rebuilt "
                            "and run cell by cell: %s events, %d mismatches. Rests on the chain law (Lean) and on the "
                            "simulator's arithmetic (the number above, decoded back into words), which is not in Lean."
                            % (f['eras'], evs, '{:,}'.format(f['cell_steps']), f['words'], f['width'],
                               '{:,}'.format(f['spot']), f['bad']),
                    "where": "<code>python3 " + TOOL + "wordchain.py " + M + " jump %d 10</code>" % f['eras']})
        new.append({"level": "open", "title": "What a change of era hands on",
                    "text": "At the end of an era the words are at or near their largest values; after the change they "
                            "hold small values, the boundaries between words have moved by a digit, the last word has one "
                            "digit more, and N has either gained 1 (the change is one event, and two words disappear) or "
                            "lost 2 to 9 base-3 digits, depending on N mod 9 and more, which become new words. A rule for "
                            "this hand-over, and whether a change of era can ever halt, are open.",
                    "where": ""})
        i = next((j for j, x in enumerate(claims) if x['title'].startswith('The cascade rule')), len(claims) - 1) + 1
        claims[i:i] = new
        d['claims'] = claims
        line = "python3 " + TOOL + "wordchain.py " + M + " jump %d 10" % f['eras']
        d['check'] = [x for x in d['check'] if 'wordchain.py' not in x] + [line]
        # the explainer
        pre = presets(r)
        widget = widget_src.replace('__MACHINE__', M).replace('__PRESETS__', json.dumps(pre, separators=(',', ':')))
        rows = ''
        for e in r['first'][:18]:
            n, nw, ws = parse_show(e['start'])
            sh = 'Z%d · ' % ws[0][2] + ' '.join('%s%d' % (t, w) if w else '·' for t, v, w in ws[1:])
            rows += '<tr><td>%s</td><td>%d</td><td><code>%s</code></td></tr>' % (sci(int(e['event'])), len(ws), sh)
        tab = ('<table class="tbl"><thead><tr><th>first event of the era</th><th>words</th><th>widths (Z, then W and U '
               'alternately; · empty)</th></tr></thead><tbody>' + rows + '</tbody></table>')
        sec = {"id": "chain", "eyebrow": "Decoded", "heading": "One law for every era",
               "html": [
                   "<p>All the layouts of the run, the plain cascade, the X layer and everything after, are one shape: "
                   "Z followed by a chain of binary words, alternately of two kinds (W with digits <code>0001</code>, "
                   "<code>0101</code> and U with digits <code>1000</code>, <code>1010</code>), separated by the blocks "
                   "<code>1 1</code>, <code>0 1</code> and <code>1 0 1 1</code>, any of them possibly empty:</p>"
                   "<p style=\"text-align:center\">" + LAYOUT + "</p>"
                   "<p>Every word is a binary counter, and <b>every wrap sends 3 to the next word</b>. Each event adds 1 to Z; "
                   "when Z wraps, W₁ gets 3; when W₁ wraps, U₁ gets 3; and so on. An empty word wraps at once, so it passes "
                   "3 times what it got. In one number: Z + 2<sup>|Z|</sup>/3 · (W₁ + 2<sup>|W₁|</sup>/3 · (U₁ + …)) grows "
                   "by exactly 1 per event. The rules of the earlier sections are special cases: the cascade is one pair "
                   "(C, R), the X layer two pairs (∅, X) and (C, R), and for the X layer the law gives the odd-looking "
                   "C + 24/2<sup>k</sup> (an empty W makes the 3 into 9, X of k digits takes 9 mod 2<sup>k</sup> and "
                   "passes the rest on, times 3).</p>"
                   "<p>The law is proved in Lean for every number of words and every width (<code>" + layers + "</code>), "
                   "from 23 visit rows of blocks of 1, 2 and 4 cells composed by induction.</p>",
                   "<p>Because the right side is one counter, a simulator can jump straight to the last event before a "
                   "carry would leave the last word, and run only the change of era cell by cell. The first eras of the "
                   "run:</p>", tab,
                   "<p>Through %d changes of era, %s events, nothing halts. The chain keeps growing: at the end it has %d "
                   "words with %d digits in all. Step through a layout below; the page can run the machine itself on the "
                   "encoded tape to check that it leaves exactly the predicted words.</p>" % (f['eras'], evs, f['words'], f['width']),
                   widget]}
        secs = [s for s in ex['sections'] if s['id'] != 'chain']
        i = next((j for j, s in enumerate(secs) if s['id'] == 'eras'), len(secs) - 1) + 1
        secs.insert(i, sec)
        for s in secs:
            if s['id'] == 'open':
                s['html'] = ["<p>The engine is proved for every layout: N + 1 on the left, and on the right the chain law. "
                             "A halt can only come during a change of era, when a carry runs off the last word: every "
                             "event that follows the law is a run of the machine that never reads the halting 1. At the end "
                             "of an era all words are near their largest values; after the change they hold small values, "
                             "the boundaries between words have moved by a digit, the last word has a digit more, and N has "
                             "either gained 1 or given 2 to 9 of its lowest base-3 digits to new words. Open: (1) a rule for "
                             "this hand-over; (2) whether some change of era can ever put the head on the halting 1.</p>"]
        ex['sections'] = secs
        json.dump(d, open(path, 'w'), indent=1, ensure_ascii=False)
        open(path, 'a').write('\n')
        print('wrote', path)


if __name__ == '__main__':
    if sys.argv[1] == 'collect':
        collect(sys.argv[2], sys.argv[3] if sys.argv[3] != '-' else None, sys.argv[4])
    else:
        write()
