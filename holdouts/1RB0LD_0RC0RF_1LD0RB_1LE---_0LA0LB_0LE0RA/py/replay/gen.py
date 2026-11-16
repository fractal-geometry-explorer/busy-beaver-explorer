"""Check the certificate of explore.py with the static engine (the Python model of lean/Exec.lean) and write the
generated Lean files.

usage (from anywhere):  python3 gen.py [CERT.json[.gz]] [--check]     (default: cert.json.gz next to this file)
  CERT.json and CERT.json.tables.json as written by explore.py.

Checks, in the model: every cycle rule by its proof run without cycle rules; every leaf of every class tree, run from
the counts that the tree gives it (static mode, variables free): K moves to the announced node (equal after `canon`),
or to a halting configuration; the halting classes (all leaves halt) and the list `pre` of leaves that run into one;
the arrival from blank tape.  Lean repeats all of it (lean/Check*.lean, lean/Arrive.lean) with its own executor.

Writes lean/ExecData.lean, lean/Data*.lean, lean/Check*.lean, lean/Arrive.lean, lean/Replay.lean.
"""
import gzip
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import engine as E  # noqa: E402
import explore as X  # noqa: E402

LEAN = os.path.join(HERE, '..', '..', 'lean')
NS = 'H163738M'
NCHUNK = int(os.environ.get('NCHUNK', '8'))


def cnt(x):
    return (x[0], tuple(x[1]))


def leaves(tree, out):
    if 'leaf' in tree:
        out.append(tree)
    else:
        for c in tree['ch']:
            leaves(c, out)
    return out


def run_static(shR, shL, rules, text, counts, K):
    e = E.Engine(shR, shL, rules, False)
    e.st = E.EV
    e.R = list(reversed(X.build(text, counts)))
    first_cross = e.cross()
    e = E.Engine(shR, shL, rules, False)
    e.st = E.EV
    e.R = list(reversed(X.build(text, counts)))
    try:
        for _ in range(K):
            e.move()
    except E.Halt:
        return 'halt', e, first_cross
    return 'ok', e, first_cross


# ---------------------------------------------------------------- encoding
def enc_cnt(n):
    return [n[0], len(n[1])] + list(n[1])


def enc_text(text):
    out = []
    parts = text.split()
    out.append(len(parts))
    for p in parts:
        if p.startswith('('):
            w = p[1:p.index(')')]
            out += [1, len(w)] + [int(c) for c in w]
        else:
            out += [0, len(p)] + [int(c) for c in p]
    return out


def enc_tree(t):
    if 'leaf' in t:
        lf = t['leaf']
        if lf[0] == 'halt':
            return [0, lf[1] - 1]
        cs = [cnt(n) for n in lf[3]]
        out = [1, lf[1] - 1, lf[2], len(cs)]
        for n in cs:
            out += enc_cnt(n)
        return out
    sp = t['split']
    k = len(t['ch'])
    if sp[0] == 'res':
        out = [2, sp[1], sp[2], k]
    elif sp[0] == 'peel':
        out = [3, sp[1], sp[2], k]
    else:
        out = [4, sp[1], sp[2]]
    for c in t['ch']:
        out += enc_tree(c)
    return out


def wrap(nums, width=120):
    s = ' '.join(map(str, nums))
    lines = []
    while len(s) > width:
        i = s.rfind(' ', 0, width)
        lines.append(s[:i])
        s = s[i + 1:]
    lines.append(s)
    return '\n'.join(lines)


def main():
    args = [a for a in sys.argv[1:] if not a.startswith('--')]
    path = args[0] if args else os.path.join(HERE, 'cert.json.gz')
    cert = json.load(gzip.open(path) if path.endswith('.gz') else open(path))
    shR, shL, rr = X.load_tables((path[:-3] if path.endswith('.gz') else path) + '.tables.json')
    log = lambda *a: (print(*a), sys.stdout.flush())
    E.SPLIT = False
    rules = []
    for M, tmpl, events, K in rr:
        q = E.Rule(M, tmpl, events)
        assert E.prove_rule(q, shR, shL, False)
        assert all(isinstance(t, int) or t[0] == 'f' or (t[2] - t[3]) % q.M == 0 for t in q.tmpl)
        rules.append(q)
    cls = cert['classes']
    big, mod = cert['big'], cert['mod']
    assert big == X.BIG and mod == X.MOD
    # halting classes
    isH = []
    for c in cls:
        kinds = {lf['leaf'][0] for lf in leaves(c['tree'], [])}
        assert 'undecided' not in kinds, c['text']
        isH.append(kinds == {'halt'})
        assert kinds == {'halt'} or 'halt' not in kinds, ('mixed class', c['text'])
    # every leaf, static
    pre = []
    nmoves = 0
    for i, c in enumerate(cls):
        for lf in leaves(c['tree'], []):
            start = [cnt(n) for n in lf['start']]
            kind = lf['leaf'][0]
            K = lf['leaf'][1]
            nmoves += K
            st, e, fc = run_static(shR, shL, rules, c['text'], start, K)
            if kind == 'halt':
                assert st == 'halt' and e.moves == K, (c['text'], start)
                continue
            j, tcs = lf['leaf'][2], [cnt(n) for n in lf['leaf'][3]]
            assert st == 'ok' and not fc and e.st == E.EV and not e.L, (c['text'], start)
            d = cls[j]
            assert E.canon(e.toks()) == E.canon(X.build(d['text'], tcs)), (c['text'], start)
            assert len(tcs) == len(d['res'])
            for n, r in zip(tcs, d['res']):
                assert n[0] >= big and all(p % mod == 0 for p in n[1]) and n[0] % mod == r % mod
            if isH[j]:
                pre.append((c['text'], start, K - 1, j, tcs))
        if i % 50 == 0:
            log('checked class %d of %d' % (i, len(cls)))
    # arrival
    a = cert['arrival']
    arr_j = [k for k, c in enumerate(cls) if [c['text'], c['res']] == a['key']]
    assert len(arr_j) == 1
    e = E.Engine(shR, shL, rules, False)
    e.st = a.get('start', 0)
    for _ in range(a['moves']):
        e.move()
    assert e.st == E.EV and not e.L
    assert E.canon(e.toks()) == E.canon(X.build(a['key'][0], [E.cst(v) for v in a['counts']]))
    assert not isH[arr_j[0]]
    log('classes %d (%d halting), leaves %d, moves %d, pre %d, cycle rules %d, arrival %d moves'
        % (len(cls), sum(isH), sum(len(leaves(c['tree'], [])) for c in cls), nmoves, len(pre), len(rules),
           a['moves']))
    for p in pre:
        log('pre: %s %s -> class %d %s' % (p[0], [E.cfmt(n) for n in p[1]], p[3], [E.cfmt(n) for n in p[4]]))
    if '--check' in sys.argv:
        return
    write(shR, shL, rules, cls, isH, pre, arr_j[0], a)


# ---------------------------------------------------------------- Lean text
def lb(w):
    return "[" + ", ".join("true" if b else "false" for b in w) + "]"


def ltmpl(tmpl):
    out = []
    for t in tmpl:
        if isinstance(t, int):
            out.append(".cell %s" % ("true" if t else "false"))
        elif t[0] == 'f':
            out.append(".fix %s %d" % (lb(t[1]), t[2]))
        else:
            out.append(".var %s %d %d" % (lb(t[1]), t[2], t[3]))
    return "[" + ",\n    ".join(out) + "]"


def srules(tab):
    out = []
    for (st, w), lst in tab.items():
        for k, u, v, c in lst:
            out.append("⟨.%s, %s, %d, %s, %s, %d⟩" % ("ABCDEF"[st], lb(w), k, lb(u), lb(v), c))
    return out


HEAD = "/-! Generated by `py/replay/gen.py`; do not edit by hand. -/\n\nnamespace %s\n\nopen TM\n\n" % NS


def put(name, parts):
    open(os.path.join(LEAN, name), "w").write("".join(parts))


def write(shR, shL, rules, cls, isH, pre, arr_j, a):
    o = ["import Exec\n\n", HEAD]
    for name, ok, tab in (("shR", "OKR", shR), ("shL", "OKL", shL)):
        rs = srules(tab)
        for i, r in enumerate(rs):
            o.append("def %s%d : SRule := %s\n" % (name, i, r))
            o.append("theorem %s%d_ok : %s%d.%s := fun _ _ => rfl\n" % (name, i, name, i, ok))
        o.append("\n/-- The shift rules to the %s. -/\ndef %sTbl : List SRule := [%s]\n\n"
                 % ("right" if name == "shR" else "left", name, ", ".join("%s%d" % (name, i) for i in range(len(rs)))))
        o.append("theorem %sTbl_ok : ∀ r ∈ %sTbl, r.%s := by\n  intro r hr\n" % (name, name, ok))
        o.append("  simp only [%sTbl, List.mem_cons, List.mem_nil_iff, or_false] at hr\n" % name)
        o.append("  rcases hr with %s\n" % " | ".join(["rfl"] * len(rs)))
        for i in range(len(rs)):
            o.append("  · exact %s%d_ok\n" % (name, i))
        o.append("\n")
    o.append("/-- The tables without cycle rules: what the cycle rules themselves are proved with. -/\n")
    o.append("def T0 : Tbl := ⟨shRTbl, shLTbl, []⟩\n\n")
    o.append("theorem T0_ok : T0.OK := ⟨shRTbl_ok, shLTbl_ok, fun _ h => absurd h List.not_mem_nil⟩\n\n")
    for i, r in enumerate(rules):
        o.append("/-- Cycle rule %d (%d events a cycle, modulus %d): `F> %s`, the counts with a variable going %s. -/\n"
                 % (i, r.events, r.M, E.fmt(r.sym(0)),
                    ", ".join("%d -> %d" % (t[2], t[3]) for t in r.tmpl if not isinstance(t, int) and t[0] == 'v')))
        o.append("def rule%d : CRule := ⟨%d,\n   %s⟩\n\n" % (i, r.M, ltmpl(r.tmpl)))
        o.append("theorem rule%d_ok : RuleOK rule%d := ruleOK_of_run T0_ok %d (by native_decide)\n\n" % (i, i, r.K))
    n = len(rules)
    o.append("/-- The tables of the replay. -/\ndef T : Tbl := ⟨shRTbl, shLTbl, [%s]⟩\n\n"
             % ", ".join("rule%d" % i for i in range(n)))
    if n == 0:
        o.append("theorem T_ok : T.OK := ⟨shRTbl_ok, shLTbl_ok, fun _ h => absurd h List.not_mem_nil⟩\n")
        o.append("\nend %s\n" % NS)
        put("ExecData.lean", o)
    else:
        write_T_ok(o, n)
    write_rest(shR, shL, rules, cls, isH, pre, arr_j, a)


def write_T_ok(o, n):
    o.append("theorem T_ok : T.OK := by\n  refine ⟨shRTbl_ok, shLTbl_ok, ?_⟩\n  intro t ht\n")
    o.append("  simp only [T, List.mem_cons, List.mem_nil_iff, or_false] at ht\n")
    o.append("  rcases ht with %s\n" % " | ".join(["rfl"] * n))
    for i in range(n):
        o.append("  · exact ⟨rule%d_ok, by decide⟩\n" % i)
    o.append("\nend %s\n" % NS)
    put("ExecData.lean", o)


def write_rest(shR, shL, rules, cls, isH, pre, arr_j, a):
    # classes, in chunks of about equal numbers of leaves
    weights = [len(leaves(c['tree'], [])) for c in cls]
    tot = sum(weights)
    bounds = [0]
    acc = 0
    for i, w in enumerate(weights):
        acc += w
        if acc >= tot * len(bounds) / NCHUNK and len(bounds) < NCHUNK:
            bounds.append(i + 1)
    if bounds[-1] != len(cls):
        bounds.append(len(cls))
    nch = len(bounds) - 1
    d = ["import Decode\n\n", HEAD]
    for k in range(nch):
        nums = []
        for i in range(bounds[k], bounds[k + 1]):
            c = cls[i]
            nums += [1 if isH[i] else 0, len(c['res'])] + list(c['res']) + enc_text(c['text']) + enc_tree(c['tree'])
        d.append("/-- Classes %d to %d. -/\ndef chunk%dS : String := \"\n%s\"\n\n" % (bounds[k], bounds[k + 1] - 1, k,
                                                                                    wrap(nums)))
        d.append("def chunk%d : List Cls := readCls chunk%dS\n\n" % (k, k))
    d.append("/-- The %d classes of the certificate. -/\n" % len(cls))
    d.append("def cls : List Cls := %s\n\n" % " ++ ".join("chunk%d" % k for k in range(nch)))
    nums = []
    for text, start, K, j, tcs in pre:
        nums += enc_text(text) + [len(start)] + sum((enc_cnt(n) for n in start), []) + [K, j, len(tcs)] + \
            sum((enc_cnt(n) for n in tcs), [])
    d.append("/-- The starts that run into a halting class. -/\ndef preS : String := \"\n%s\"\n\n" % wrap(nums))
    d.append("def pre : List PreE := readPre preS\n\n")
    d.append("theorem cls_length : cls.length = %d := by native_decide\n\n" % len(cls))
    d.append("end %s\n" % NS)
    put("Data.lean", d)
    for k in range(nch):
        put("Check%d.lean" % k, ["import ExecData\nimport Data\n\n", HEAD,
            "/-- Every class of the chunk: every split of its tree well formed, every leaf one run of the executor. -/\n"
            "theorem chunk%d_ok : chunk%d.all (clsOK cls pre T) = true := by\n  native_decide\n\n"
            "end %s\n" % (k, k, NS)])
    put("Arrive.lean", ["import ExecData\nimport Data\n\n", HEAD,
        "/-- %d moves of the executor from blank tape end at a node of class %d (not a halting class). -/\n"
        % (a['moves'], arr_j),
        "theorem arrive_ok : arrives cls T %d %d [%s] = true := by\n  native_decide\n\n"
        % (a['moves'], arr_j, ", ".join(map(str, a['counts']))),
        "theorem pre_ok : pre.all (preOK cls T) = true := by\n  native_decide\n\nend %s\n" % NS])
    r = ["import Arrive\n" + "".join("import Check%d\n" % k for k in range(nch)), '''
/-!
# The mirror machine (`MachineM.lean`) halts if and only if its run reaches a start of `pre`

Generated by `py/replay/gen.py` (the text is fixed; only the number of chunks is filled in).
-/

namespace %s

open TM

theorem cls_all : cls.all (clsOK cls pre T) = true := by
  show (%s).all (clsOK cls pre T) = true
  simp only [List.all_append, %s, Bool.and_self]

theorem cls_ok : ∀ c ∈ cls, clsOK cls pre T c = true := fun c hc => List.all_eq_true.1 cls_all c hc

/-- **Halting from blank tape, reduced to the list `pre`**: the machine halts if and only if its run reaches the node
of an entry of `pre` (for some value of its variables). -/
theorem halts_iff_pre : HaltsFromBlank ↔ ∃ p ∈ pre, ∃ ρ, Reach init (nodeCfg p.text (evals ρ p.cs)) :=
  halts_iff_of_checks T_ok cls_ok (fun p hp => List.all_eq_true.1 pre_ok p hp) (arrives_sound T_ok arrive_ok)

end %s
''' % (NS, " ++ ".join("chunk%d" % k for k in range(nch)), ", ".join("chunk%d_ok" % k for k in range(nch)), NS)]
    put("Replay.lean", r)
    put("check.sh", ["""#!/bin/bash
# Check this machine's Lean files with the shared library (tools/lean). LEAN, LEANLIB as for tools/lean/check.sh.
# Written by py/replay/gen.py.  The %d class checks (Check*.lean, native_decide) run in parallel, JOBS at a time.
set -e
cd "$(dirname "$0")"
../../../tools/lean/check.sh . Machine.lean Blank.lean Rules.lean MachineM.lean Exec.lean Pieces.lean \\
  Decode.lean ExecData.lean Data.lean Arrive.lean
LEAN=${LEAN:-lean}
if [ -z "$LEANLIB" ]; then LEANLIB="$(dirname "$(command -v "$LEAN")")/../lib/lean"; fi
export LEAN_PATH="$LEANLIB:../../../tools/lean/out:$(pwd)/out"
JOBS=${JOBS:-$(nproc)}
ls Check*.lean | xargs -P "$JOBS" -I{} sh -c 'echo "== {}"; $0 {} -o out/$(basename {} .lean).olean' "$LEAN"
for f in Replay Mirror Final; do echo "== $f.lean"; $LEAN $f.lean -o out/$f.olean; done
echo "ALL CHECKED"
""" % nch])
    os.chmod(os.path.join(LEAN, 'check.sh'), 0o755)

if __name__ == "__main__":
    main()
