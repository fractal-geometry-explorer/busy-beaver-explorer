"""Run the machine concretely from PS a c / Q R m c (see lean/Phases.lean) and print the first PS or Q configuration
it reaches, or the halt.  This is how the cases of the phase map were found.

usage: python3 classify.py Q R m c   |   python3 classify.py PS a c
"""
import re, sys
sys.path.insert(0, __import__('os').path.dirname(__import__('os').path.abspath(__file__)))
import sim
M = '1RB1RF_1LC1LF_0RE1LD_0LB1LD_---1RC_1RA0RD'
T = sim.parse_m(M)
def Q(R, m, c): return f"{'1 0 '*R}{'1 1 '*m}A> {'1 '*c} 0"
def PS(a, c): return f"B> 0 0 {'1 0 '*a}{'1 '*c} 0"
def classify(tape, h, st):
    lo, hi = min(min(tape), h), max(max(tape), h)
    L = ''.join(str(tape.get(i, 0)) for i in range(lo, h)).lstrip('0')
    Rr = ''.join(str(tape.get(i, 0)) for i in range(h, hi + 1)).rstrip('0')
    if st == 0:
        m1 = re.fullmatch(r'((?:10)*)((?:11)*)', L); m2 = re.fullmatch(r'(1+)', Rr)
        if m1 and m2: return ('Q', len(m1.group(1))//2, len(m1.group(2))//2, len(m2.group(1)))
    if st == 1 and L == '':
        m2 = re.fullmatch(r'00((?:10)*)(1*)', Rr+'00'*(len(Rr)<2))
        if m2: return ('PS', len(m2.group(1))//2, len(m2.group(2)))
        if Rr in ('', '0'): pass
    return None
def nxt(s, maxsteps=10**6):
    res = sim.run(T, s, maxsteps, stop=lambda tp, h, st, k: classify(tp, h, st) is not None)
    if res[0] == 'halt': return ('halt', res[1])
    if res[0] == 'run': return ('run',)
    return classify(res[2], res[3], res[4]) + (res[1],)
if __name__ == '__main__':
    kind = sys.argv[1]; args = [int(x) for x in sys.argv[2:]]
    s = Q(*args) if kind == 'Q' else PS(*args)
    print(nxt(s))
