from absim2 import round_step, Halt
import json
def f(n, maxrounds=100000, log=None):
    """Next clean n from clean n (state at round start: w = 2n+6, G1, M at w-2)."""
    w = 2 * n + 6; marks = [('G', 1), ('M', w - 2)]
    for r in range(maxrounds):
        w, marks = round_step(w, marks, log)
        if len(marks) == 2 and marks[1] == ('M', w - 2):
            return (w - 6) // 2, r + 1
    raise RuntimeError("no clean")
if __name__ == "__main__":
    d = json.load(open('../m2/clean3e9.json'))
    ns = [n for s, n, k in d]
    bad = [(a, b, f(a)) for a, b in zip(ns, ns[1:]) if f(a)[0] != b]
    print("checked", len(ns) - 1, "transitions; mismatches:", bad[:5])
