import sys
import rlf, rlg, far
from rlctl import Machine
mt = sys.argv[1]; mir = sys.argv[2] == "R"
M, c1, c0, cg = map(int, sys.argv[3:7]); steps = int(float(sys.argv[7])); feats = sys.argv[8]; m1, mg = int(sys.argv[9]), int(sys.argv[10])
if mir: mt = far.mirror(mt)
side = rlg.GSide(M, c1, c0, cg, feats, m1, mg)
m = Machine.parse(mt)
N = 1 << 22
tape = bytearray(N); Ls = [0] * N
p = N // 2; s = 0
marks = [steps // 8, steps // 4, steps // 2, steps]
for step in range(1, steps + 1):
    t = m.table[s][tape[p]]
    w, d, s2 = t
    tape[p] = w
    if d == 1:
        Ls[p] = side.push(Ls[p - 1], w)[0]
        p += 1
    else:
        p -= 1
    s = s2
    if step in marks: print(step, len(side.states), len(side.edges), flush=True)
ok, delta, T, HALT = far.far(m, side, True)
print("PROVED" if ok else "no proof", sys.argv[2:])
