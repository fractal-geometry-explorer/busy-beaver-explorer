"""Validate the closed node set of search.py against the real run, and mutation-test that validation.

1. Runs the search (with the ratio rules of witness_1e300.json, start = exact run at step ~2e20).
2. Follows the exact accelerated run from the blank tape (py/accel.py) up to MAXSTEPS.  At every event after
   the start step it looks the configuration up among the nodes (same block shape, constants equal, free
   counts >= threshold).  It reports
     * how many node visits there were and how many different nodes were visited,
     * the walk through the node graph: the current node changes only along an edge found by the search.
       The search can hold the same phase as several nodes (the shape at different points of the period), so a
       node with the same delta as the current one is added to the current set; any other node shape met where
       there is no edge from the current set is counted as "in passing",
     * every phase jump of >= 1000 periods: is the current node one whose delta is the jump's delta?
       (if the search missed a transition, the walk stays behind and the next jump does not match)
     * the smallest real size of a block that a node calls huge.
3. DEFECT=name plants a defect in the search (see search.DEFECT) or DEFECT=flip_ratio swaps the ratio rule of
   the drain phase; the validation must then report a failure (missing edge / uncovered jump / search not closed).

usage (from the repo root): [DEFECT=...] python3 holdouts/<M>/py/closure2/validate.py MACHINE MAXSTEPS
"""
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import search  # noqa: E402
from search import accel  # noqa: E402


def main():
    M = sys.argv[1]
    mx = int(float(sys.argv[2]))
    defect = os.environ.get('DEFECT')
    ratio = json.load(open(os.path.join(HERE, 'witness_1e300.json')))['signatures']
    if defect == 'flip_ratio':
        ratio['-18,18,36,-11']['first'] = {'0': 1}
    elif defect == 'no_ratio':
        ratio = {}
    elif defect:
        search.DEFECT[0] = defect
    search.RATIO.update(ratio)
    start, step0, txt = search.start_from_run(M, 1e20)
    S = search.Search(M, 4000, start=start)
    closed = S.run(tmax=float(os.environ.get('TMAX', 300)))
    print('search: %s, nodes %d, branches %d, halting branches %d, stuck %d, queue %d' %
          ('closed' if closed else 'NOT closed', len(S.info), S.branches, len(S.halts), len(S.stuck), len(S.queue)))
    edges = set((a, b) for a, b, lab in S.edges)
    delta = {n['id']: tuple(x for x in n['delta'] if x) for n in S.info}

    accel.CROSS_EVENTS[0] = True
    accel.CROSS_MIN[0] = search.BIG
    R = accel.Sim(M)
    st = {'visits': 0, 'cur': set(), 'alias': 0, 'pending': None, 'ignored': 0, 'changes': 0, 'jumps': 0, 'jumps_bad': 0, 'minhuge': None}
    seen = set()
    badlist = []

    def on_event(s):
        c = s.c
        if c.steps < step0:
            return
        cand = S.nodes.get(accel.shape(c))
        if not cand:
            return
        cn = [z.n for z in accel.reps(c)]
        for t, i in cand:
            # a block the node calls huge must have >= HMIN copies, except the blocks that shrink in the node's
            # phase: the exact run jumps to the last periods of a phase at once, where they are nearly used up
            dl = S.info[i]['delta']
            if all((a == 'c' and n == x) or (a == 'v' and n >= x) or
                   (a == 'H' and n >= (x if dl[j] < 0 else max(x, search.HMIN)))
                   for j, ((a, x), n) in enumerate(zip(t, cn))):
                break
        else:
            return
        st['visits'] += 1
        cur = st['cur']
        if i in cur:
            return
        if not cur or any((a, i) in edges for a in cur):
            st['cur'] = cur = {i}                 # a step along an edge of the node graph
            st['changes'] += 1
        elif delta[i] == delta[next(iter(cur))]:
            cur.add(i)                            # the same phase seen at another point of its period
            st['alias'] += 1
        else:
            st['ignored'] += 1                    # the shape of a node met in passing
            return
        for j, ((a, x), n) in enumerate(zip(t, cn)):
            if a == 'H' and dl[j] >= 0 and (st['minhuge'] is None or n < st['minhuge']):
                st['minhuge'] = n
        seen.add(i)
        if delta[i] == st['pending']:
            st['pending'] = None

    def on_jump(rule, k):
        if R.c.steps < step0 or k < 1000:
            return
        st['jumps'] += 1
        if st['pending'] is not None:
            st['jumps_bad'] += 1
            if len(badlist) < 5:
                badlist.append('%.3e: the phase with delta %s ended while the walk was still in node %s' %
                               (R.c.steps, st['pending'], sorted(st['cur'])))
        d = tuple(x for x in rule[2] if x)
        # the exact run jumps as soon as it knows the phase; the node of the search is met in the periods that
        # the jump leaves over (at least one), so the check is made when the next long jump starts
        st['pending'] = None if any(delta[a] == d for a in st['cur']) else d
    R.on_jump = on_jump
    R.run(mx, on_event=on_event)
    print('real run to %.3e: node visits %d (%d in passing, not along an edge), steps along edges %d, same phase at another point %d, '
          'different nodes %d of %d, long jumps %d, long jumps outside a matching node %d, smallest block '
          'called huge %s' % (R.c.steps, st['visits'], st['ignored'], st['changes'], st['alias'], len(seen), len(S.info),
                              st['jumps'], st['jumps_bad'], st['minhuge']))
    for b in badlist:
        print('  ', b)
    ok = closed and not S.halts and not S.stuck and st['jumps_bad'] == 0 and st['jumps'] > 0
    print('VALIDATION', 'OK' if ok else 'FAILED', '(defect: %s)' % defect if defect else '')


if __name__ == '__main__':
    main()
