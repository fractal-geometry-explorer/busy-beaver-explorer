"""Differential test of the simulators against the proved mark model.

Every simulator and the oracle (Oracle.lean: `roundZ`, proved against the machine in ../lean/BB6/Round.lean) run the
same random well-formed round starts for NR rounds.  Where both make a claim (a round start, or a halt) they must agree;
U means the program makes no claim from there on (a configuration outside its rules, or a checker's early stop at a
close).  Reports, per simulator: rounds compared, disagreements (with the first few), and rounds claimed by the
simulator where the oracle makes no claim (not checked).

With --canon, a simulator's round start is first brought to canonical form (a wall in the last two cells, one past
the width, is the same tape as no wall and width W - 1), so that only different tapes count as disagreements.

ORACLE=command replaces the oracle, e.g. ORACLE="node stepper.js 12 machine" (the bare machine, small tapes only).

usage: python3 run.py [--canon] N SEED NR SIM...      SIM is name=command (reads starts, writes rounds)
example: see check.sh"""
import subprocess, sys, os, tempfile
here = os.path.dirname(os.path.abspath(__file__))

def blocks(text):
    out, cur = [], []
    for l in text.split('\n'):
        if l == '.': out.append(cur); cur = []
        elif l: cur.append(l)
    return out

def run(cmd, starts):
    r = subprocess.run(cmd, shell=True, input=starts, capture_output=True, text=True)
    if r.returncode: sys.exit('%s failed: %s' % (cmd, r.stderr[-2000:]))
    return blocks(r.stdout), r.stderr

def canon(s):
    w = s.split()
    if len(w) >= 4 and w[-2] == 'W' and int(w[-1]) + 1 == int(w[1]): w = ['R', str(int(w[1]) - 1)] + w[2:-2]
    return ' '.join(w)

def main():
    args = sys.argv[1:]; can = '--canon' in args; args = [a for a in args if a != '--canon']
    n, seed, nr = map(int, args[:3]); sims = [a.split('=', 1) for a in args[3:]]
    starts = subprocess.run([sys.executable, os.path.join(here, 'gen.py'), str(n), str(seed)], capture_output=True,
                            text=True, check=True).stdout
    lines = starts.strip().split('\n')
    lean = os.environ.get('LEAN', 'lean')
    oracle, _ = run(os.environ.get('ORACLE') or '%s --run %s %d' % (lean, os.path.join(here, 'Oracle.lean'), nr), starts)
    assert len(oracle) == n
    status = 0
    for name, cmd in sims:
        res, err = run(cmd, starts); assert len(res) == n, name
        cmp_ = dis = extra = 0; ex = []
        for i in range(n):
            o, s = oracle[i], res[i]
            for k in range(min(len(o), len(s))):
                if o[k] in 'UE' or s[k] in 'UE':
                    if o[k] == 'U' and s[k] not in 'UE': extra += len(s) - k - (s[-1] in 'UE')
                    break
                cmp_ += 1
                if o[k] != (canon(s[k]) if can else s[k]):
                    dis += 1
                    if len(ex) < 5: ex.append('start "%s", round %d: model %s, %s %s' % (lines[i], k + 1, o[k], name, s[k]))
                    break
                if o[k] == 'H': break
        print('%-10s rounds compared %7d, disagreements %d, rounds beyond the model (unchecked) %d' % (name, cmp_, dis, extra))
        for e in ex: print('    ' + e)
        for l in err.strip().split('\n'):
            if l: print('    [%s] %s' % (name, l))
        if dis: status = 1
    sys.exit(status)

main()
