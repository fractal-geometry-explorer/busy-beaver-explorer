"""Check the complete macro map `mstep` of a sister machine (lean/Sim.lean) against the accelerated run.

  python3 check_mstep.py MACHINE run [NTRANSIENTS]   along hyb.py's run from blank tape (default 300 transients),
      give the Q configuration before each irregular stretch to Lean's `mstep` (evaluated by `lean --run`) and
      compare its answer with the cell-by-cell simulation of c/trans.c: they must agree, and `mstep` never fails.
  python3 check_mstep.py MACHINE count K   run `mstep` K times from `start` (step 27) and print how many of the
      steps were simulated stretches (`tstep`) rather than closed forms (`astep`).

Needs the machine's Lean files compiled (lean/check.sh) and LEAN, LEANLIB set as for tools/lean/check.sh.
"""
import os
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from hyb import Nphi, comp, from_blank, jcoll, jump, transient  # noqa: E402

REPO = os.path.join(HERE, "../../..")


def to_wag(W, k, q, g, rest):
    a, P = comp(k, q)
    return list(W), a, [3 * p - 1 for p in P] + ([g] + rest if g is not None else [])


def lean_run(m, body, inp):
    d = os.path.join(REPO, "holdouts", m, "lean")
    ns = next(l.split()[1] for l in open(os.path.join(d, "Machine.lean")) if l.startswith("namespace "))
    lean = os.environ.get("LEAN", "lean")
    lib = os.environ.get("LEANLIB") or os.path.join(os.path.dirname(subprocess.check_output(
        ["which", lean], text=True).strip()), "../lib/lean")
    env = dict(os.environ, LEAN_PATH=":".join([lib, os.path.join(REPO, "tools/lean/out"), os.path.join(d, "out")]))
    with tempfile.NamedTemporaryFile("w", suffix=".lean", delete=False) as f:
        f.write(f"import Sim\nopen {ns}\n" + body)
    try:
        p = subprocess.run([lean, "--run", f.name], input=inp, capture_output=True, text=True, env=env)
        if p.returncode:
            sys.exit(p.stdout + p.stderr)
        return p.stdout
    finally:
        os.unlink(f.name)


RUN = r'''
def nums (s : String) : List Nat := ((s.splitOn ",").filter (· ≠ "")).map String.toNat!
def showC (c : AC) : String := s!"{c.W} {c.a} {c.G}"
partial def loop (h : IO.FS.Stream) (o : IO.FS.Stream) : IO Unit := do
  let l ← h.getLine
  if l.isEmpty then return
  match (l.trimAscii.toString.splitOn ";") with
  | [w, a, g] =>
    let c : AC := ⟨nums w, a.toNat!, nums g⟩
    let k := if (astep c).isSome then "astep" else "tstep"
    match mstep c with
    | some c' => o.putStrLn s!"{k} {showC c'}"
    | none => o.putStrLn "FAIL"
  | _ => o.putStrLn "BAD"
  o.flush
  loop h o
def main : IO Unit := do loop (← IO.getStdin) (← IO.getStdout)
'''

COUNT = r'''
def cnt : Nat → Nat → AC → Nat × Nat
  | 0, t, _ => (0, t)
  | k + 1, t, c => match astep c with
    | some c' => cnt k t c'
    | none => match tstep c with
      | some c' => cnt k (t + 1) c'
      | none => (k + 1, t)
def main (args : List String) : IO Unit := do
  let r := cnt args.head!.toNat! 0 start
  IO.println (if r.1 = 0 then s!"all steps succeed; simulated stretches {r.2}"
    else s!"FAILED with {r.1} steps left; simulated stretches {r.2}")
'''


def run(m, n):
    st = from_blank(m)
    pre, exp = [], []
    for e in range(n):
        W, k, q, g, rest, _ = st
        Ja, Jc = Nphi(W) // 2, jcoll(k, q, g)
        st = jump(st, Ja if Jc is None else min(Ja, Jc))
        r = transient(m, st, 10 ** 11)
        if r[0] != 'OK':
            print('transient', r[0])
            break
        pre.append(to_wag(*st[:5]))
        exp.append(to_wag(*r[1][:5]))
        st = r[1]
    inp = "".join(f"{','.join(map(str, reversed(W)))};{a};{','.join(map(str, G))}\n" for W, a, G in pre)
    out = lean_run(m, RUN, inp).strip().split("\n")
    kinds, bad = {}, 0
    for (W, a, G), line in zip(exp, out):
        if line == "FAIL":
            bad += 1
            continue
        kind, rest = line.split(" ", 1)
        kinds[kind] = kinds.get(kind, 0) + 1
        want = f"{list(reversed(W))} {a} {G}".replace(" ", "")
        if rest.replace(" ", "") != want:
            bad += 1
    print(m, len(out), "irregular stretches:", kinds, "disagreements or failures:", bad)


def main():
    m, mode = sys.argv[1], sys.argv[2]
    if mode == "run":
        run(m, int(sys.argv[3]) if len(sys.argv) > 3 else 300)
    else:
        print(lean_run(m, COUNT.replace("args.head!", f'"{sys.argv[3]}"').replace("(args : List String) ", ""), "")
              .strip())


if __name__ == "__main__":
    main()
