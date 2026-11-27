"""Which walls stand at the far end of the draining ternary odometer, and how close the run comes to the halting
route (26 November 2026).

Runs the exact accelerator py/oacc.py and, after every macro step, looks at the top wall (the first wall from the
far end), the wall below it and every wall that is not a counter wall Z, O, T.  A cycle jump repeats shapes that
two explicit periods have already shown, so every wall and every pair (top wall, wall below) that occurs is seen.

The halting route found on synthetic tapes (holdouts/recent-proofs/nested-counter-levels-nov26.md): top wall
`b1_2` with a middle gadget `b2_3` of run 0 directly below fuses to the top wall `b3_1`, which a carry turns into
`b2_2`; if the first digit then has run 0, the top becomes `b2_4` and the next carry halts.

    python3 py/topwalls.py START SECONDS OUT.json [c1]
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import oacc  # noqa: E402

C = oacc.C
NAMES = {'c2': '1RB0LD_1RC0RF_1LA1RF_0LA0RE_1LD---_0RA0RD', 'c1': '1RB---_0RC0LA_1LD0RB_1LE0LF_1RC1LF_0LC0LB'}
DANGER = ('b3_1', 'b2_2', 'b2_4', 'b3_4', 'b4_1', 'b4_2', 'b4_3', 'b4_4', 'b4_5')


def main():
    a = sys.argv[1:]
    which = 'c1' if 'c1' in a else 'c2'
    C.use(which)
    a = [x for x in a if x not in ('c1', 'c2')]
    seconds, out = float(a[1]), a[2]
    (st, T), n0 = C.start_state(a[0]), 0
    e = oacc.Engine(st, T, n0)
    walls, tops, pairs, danger = {}, {}, {}, []
    gadget_min = None      # smallest run of a b2_3 directly below the top wall b1_2, with the run below it
    macro = 0
    t0 = time.time()

    def note(d, k, extra=None):
        r = d.get(k)
        if r is None:
            d[k] = r = {'first_step': '%.4e' % e.T, 'count': 0, 'first': C.DG.show(e.st)[:160]}
        r['count'] += 1
        r['last_step'] = '%.4e' % e.T

    halted = None
    while time.time() - t0 < seconds:
        try:
            e.step()
        except Exception as ex:      # a symbolic sweep that halts or fails stops the run here
            halted = repr(ex)[:300]
            break
        macro += 1
        dg = e.st[1]
        top = dg[0][0]
        note(tops, top)
        if len(dg) > 1:
            note(pairs, top + ' ' + dg[1][0] + ('(run 0)' if dg[1][1] == 0 else ''))
            if top == 'b1_2' and dg[1][0] == 'b2_3':
                below = dg[2][1] if len(dg) > 2 else e.st[2]
                if gadget_min is None or dg[1][1] < gadget_min[0]:
                    gadget_min = (dg[1][1], below, '%.4e' % e.T, C.DG.show(e.st)[:160])
        for w, r in dg:
            if w not in 'ZOT':
                note(walls, w)
        if top in DANGER or any(w in DANGER for w, _ in dg):
            if len(danger) < 200:
                danger.append(['%.4e' % e.T, C.DG.show(e.st)[:200]])
    res = {'machine': NAMES[which], 'start': a[0], 'end_step': '%.4e' % e.T,
           'sweeps': e.n, 'macro_steps': macro, 'stopped': halted, 'top_walls': tops, 'top_and_next': pairs,
           'odd_walls': walls, 'danger_events': danger, 'smallest_b2_3_under_b1_2': gadget_min,
           'end_state': C.DG.show(e.st)[:400]}
    with open(out, 'w') as f:
        json.dump(res, f, indent=1)
    print(json.dumps({k: res[k] for k in ('end_step', 'macro_steps', 'stopped')}))


if __name__ == '__main__':
    main()
