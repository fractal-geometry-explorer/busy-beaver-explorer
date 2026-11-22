"""gen_js.py: the 78 cases of `next` (lean/Phases.lean) with their step counts (lean/Pieces.lean) as a JavaScript
function on BigInt, for the jump-map panel of the explainer page (status.json, section "jumps").
    python3 py/gen_js.py            # prints the function
    python3 py/gen_js.py --check    # exit 1 if status.json does not hold the current text"""
import json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from rules import CASES

def js_expr(e):
    return re.sub(r'\b(\d+)\b', r'\1n', e)

def build():
    out = ['function fcStep(t, a, b, c) {']
    for idx, (cn, pats, tgt, st, _) in enumerate(CASES):
        conds, binds = ['t === "%s"' % cn], []
        for p, x in zip(pats, 'abc'):
            if p.isdigit(): conds.append('%s === %sn' % (x, p))
            else:
                m = re.match(r'\((\w+) \+ (\d+)\)', p)
                if m:
                    conds.append('%s >= %sn' % (x, m.group(2))); binds.append('const %s = %s - %sn;' % (m.group(1), x, m.group(2)))
                else:
                    binds.append('const %s = %s;' % (p, x))
        if tgt is None:
            ret = 'return [null, 0n, 0n, 0n, %s, %d];' % (js_expr(st), idx)
        else:
            ret = 'return ["%s", %s, %s, %s, %s, %d];' % (tgt[0], js_expr(tgt[1][0]), js_expr(tgt[1][1]), js_expr(tgt[1][2]),
                                                       js_expr(st), idx)
        out.append('  if (%s) { %s %s }' % (' && '.join(conds), ' '.join(binds), ret))
    out.append('  throw new Error("no case");')
    out.append('}')
    out.append('const FC_NAME = %s;' % json.dumps(['%s %s' % (cn, ' '.join(p)) for cn, p, *_ in CASES]))
    return '\n'.join(out)

if __name__ == '__main__':
    src = build()
    if '--check' in sys.argv:
        st = json.load(open(os.path.join(HERE, '..', 'status.json')))
        txt = json.dumps(st)
        ok = all(line in txt for line in [json.dumps(l)[1:-1] for l in src.splitlines()])
        print('status.json holds the current cases' if ok else 'status.json is out of date: rerun py/gen_js.py')
        sys.exit(0 if ok else 1)
    print(src)
