"""Write lean/XRules.lean and lean/XMap.lean for a sister machine of 1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---: the
irregular Q-steps that the machine's `astep` (Full.lean) leaves out, found by symbolic case splitting (`xleaves.py`),
each proved for all values of its parameters, and the closed-form macro map `bstep` built from them.

* XRules.lean: one tape rule per case, proved by `bbtools.symtm.prove`.
* XMap.lean: the rules restated on word-and-counter configurations (normal-form `simp`, as in CollideQ.lean), the
  decision functions `xcoll` (collisions) and `xanu` (the anomaly with a one-unit counter) by pattern matching on
  the run-length form `rl` of the gap list, the anomaly inside the word (`inner_step`), and `bstep` = `astep`,
  else these rules, with `bstep_sound` and `not_halts_of_brun`.

usage (from the repository root):
  python3 holdouts/1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---/py/gen_xmap.py MACHINE
"""
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file, Rep, Ctx, Blank, Lin  # noqa: E402
from xleaves import leaves, word_expr, gap_expr, seg_pat, ln, PErr  # noqa: E402

B = {0: "false", 1: "true"}


def lst(w):
    return "[" + ", ".join(B[c] for c in w) + "]"


def rotations(w):
    return {w[i:] + w[:i] for i in range(len(w))}


def nf_lemmas(words):
    ws = set()
    for w in words:
        for v in (w, tuple(reversed(w)), w + w, w + w + w):
            ws |= rotations(v)
    out, names = [], []
    for k, w in enumerate(sorted(ws, key=lambda x: (len(x), x))):
        b, v = w[-1], w[:-1]
        name = f"xnf{k}"
        names.append(name)
        out.append(f"theorem {name} (n : Nat) (X : Tape) :\n    cons {B[b]} (rep n {lst(w)} X) = rep n {lst((b,) + v)} "
                   f"(cons {B[b]} X) :=\n  rep_rotate n [{B[b]}] {lst(w)} {lst((b,) + v)} rfl X\n")
    # uniform words commute: the longer one is moved outward
    uni = sorted({w for w in ws if len(set(w)) == 1}, key=lambda x: (x[0], len(x)))
    for i, u in enumerate(uni):
        for w in uni[i + 1:]:
            if w[0] != u[0]:
                continue
            name = f"xcm{len(names)}"
            names.append(name)
            out.append(f"theorem {name} (m n : Nat) (X : Tape) :\n    rep m {lst(u)} (rep n {lst(w)} X) = rep n {lst(w)} "
                       f"(rep m {lst(u)} X) :=\n  rep_comm m n {lst(u)} {lst(w)} rfl X\n")
    return out, names


def rep_words(cfg):
    for t in list(cfg.left) + list(cfg.right):
        if isinstance(t, Rep):
            yield t.word


NF_BASE = ("qr, qx, zc, gl, wl, wlx, flat, Sg.gs, gl_rep, gl_rep_blank, wlx_rep, wl_append, wlx_append, rep_mul2, "
           "rep_mul3, rep_add, rep_succ, rep_zero, app_cons, app_nil, cons_false_blank, List.replicate_succ, "
           "List.replicate_zero, List.cons_append, List.nil_append, List.append_nil, List.append_assoc, Nat.add_zero")


MEM = "List.mem_cons, List.mem_append, List.mem_replicate, List.not_mem_nil, List.mem_singleton, or_false, false_or, ne_eq"
NMIS = ("simp only [flat, Sg.gs, nmis_append, nmis, nmis_rep, List.cons_append, List.nil_append, "
        "List.singleton_append, List.append_assoc, List.append_nil]\n      repeat' split\n      all_goals omega")


class TrieErr(Exception):
    pass


def build_trie(leaves_):
    root = {}
    for segs, ctx in leaves_:
        node = root
        for kind, n in segs:
            node = node.setdefault((kind, str(n), n), {})
        node[('S',) if ctx else ('end',)] = None
    return root


def trie_alts(node, prefix, prev, out):
    """Patterns (prefix list of segment patterns) with 'leaf' or 'bad' (okS false)."""
    keys = list(node)
    if ('S',) in keys:
        if len(keys) != 1:
            raise TrieErr(f"wildcard with siblings at {prefix}")
        out.append((prefix + ["S"], 'leaf'))
        return
    if ('end',) in keys:
        out.append((prefix + ["[]"], 'leaf'))
    else:
        raise TrieErr(f"no blank-tape case at {prefix}")
    for kind in ('two', 'five', 'big', 'odd'):
        ks = [k for k in keys if k[0] == kind]
        if kind == 'odd':
            out.append((prefix + [".odd _", "_"], 'bad'))
            continue
        if kind == prev:
            out.append((prefix + [f".{kind} _", "_"], 'bad'))
            continue
        if kind == 'big':
            if not ks:
                raise TrieErr(f"no big gap case at {prefix}")
            for k in ks:
                if not (len(k[2].c) == 1 and k[2].k == 0):
                    raise TrieErr(f"split big gap at {prefix}")
                trie_alts(node[k], prefix + [f".big {ln(k[2])}"], kind, out)
            continue
        consts = sorted(k[2].k for k in ks if k[2].is_const())
        vark = [k for k in ks if not k[2].is_const()]
        if len(vark) != 1:
            raise TrieErr(f"{kind} counts at {prefix}: {[k[1] for k in ks]}")
        lo = vark[0][2].k
        for c in range(lo):
            if c not in consts:
                if c != 0:
                    raise TrieErr(f"{kind} count {c} missing at {prefix}")
                out.append((prefix + [f".{kind} 0", "_"], 'bad'))
        for k in ks:
            trie_alts(node[k], prefix + [f".{kind} {ln(k[2])}"], kind, out)


def total_thm(name, args, concl, leaves_by_head):
    lines = []
    for head, lv in leaves_by_head.items():
        alts = []
        trie_alts(build_trie(lv), [], None, alts)
        for pat, kind in alts:
            ps = " :: ".join(pat)
            hp = f"{head[0]}, {head[1]}, " if head is not None else ""
            pre = "_, " + hp + ps
            if head is not None:
                pre += ", _, _"
            if kind == 'leaf':
                lines.append(f"  | {pre}, _ => rfl")
            else:
                lines.append(f"  | {pre}, h => by simp [okS, notTwo, notFive] at h")
    if any(h is not None for h in leaves_by_head):
        lines.append("  | _, _ + 2, _, _, hp, _, _ => absurd hp (by omega)")
        lines.append("  | _, 0, _ + 2, _, _, hg, _ => absurd hg (by omega)")
        lines.append("  | _, 1, _ + 2, _, _, hg, _ => absurd hg (by omega)")
    vs = args.replace("(", "").replace(")", "")
    return f"theorem {name} : ∀ {args}, {concl}\n" + "\n".join(lines) + "\n"


def binders(vs, extra=""):
    return (f"({' '.join(vs)} : Nat)" if vs else "") + extra


def main():
    m = sys.argv[1]
    d = os.path.join(HERE, "../../", m, "lean")
    ns = re.search(r"^namespace (\w+)", open(os.path.join(d, "Machine.lean")).read(), re.M).group(1)
    lv = leaves(m)
    bad = [x for x in lv if x['kind'] != 'rule']
    if bad:
        sys.exit(f"{len(bad)} cases are not rules: {bad[0]['head']} {bad[0]['leaf']}")
    rules, qlem, words = [], [], set()
    coll_alts, anu_alts, coll_pf, anu_pf = [], [], [], []
    inner = {}
    counters = {}
    coll_leaves, anu_leaves, coll_inv = {}, [], []
    for x in lv:
        hk, lf, s, e = x['head'], x['leaf'], x['start'], x['end']
        if hk[0] == 'coll':
            key = f"c{hk[1]}{hk[2]}"
        elif hk[0] == 'anu':
            key = "u"
        else:
            key = "i"
        k = counters.get(key, 0)
        counters[key] = k + 1
        rid = f"{key}_{k}"
        txt, fin = prove(m, "xr_" + rid, lf.start, lf.end, count_first=True, max_seg=40, rotate=True,
                         doc=f"case {rid} of the irregular steps (found by xleaves.py)")
        rules.append(txt)
        for w in list(rep_words(lf.start)) + list(rep_words(fin)):
            words.add(w)
        N = fin.steps.lean()
        vs = sorted(lf.start.vars() | lf.end.vars())
        tail = s['tail']
        a2 = ln(e['a'])
        if hk[0] == 'inner':
            G2 = gap_expr(e['gaps'], "G" if isinstance(e['tail'], Ctx) else "[]")
        else:
            G2 = gap_expr(e['gaps'], "flat S" if isinstance(e['tail'], Ctx) else "[]")
        ctx_args = []
        if isinstance(lf.start.left[0], Ctx):
            ctx_args.append("(L := L)")
        if isinstance(tail, Ctx):
            ctx_args.append(f"({tail.name} := " + ("gl G)" if hk[0] == 'inner' else "gl (flat S))"))
        call = f"xr_{rid} " + " ".join(f"({v} := {v})" for v in vs) + " " + " ".join(ctx_args)
        pat = seg_pat(x['segs'], tail)
        if hk[0] == 'coll':
            p, g = hk[1], hk[2]
            it = e['items']
            j = it[0]
            if j[0] != 'v' or not j[1].is_const():
                raise PErr(f"junction {j}")
            jn = j[1].k
            C = word_expr(it[1:])
            bnd = binders(vs, (" (S : List Sg)" if isinstance(tail, Ctx) else "") + " (L : Tape)")
            stmt = (f"steps ({N}) (zc L (List.replicate (2 * s + {p}) 2 ++ {g} :: flat ({pat}))) = "
                    f"some (qx {a2} ({C}) (rep {jn} [true] L) ({G2}))")
            qlem.append(f"theorem xq_{rid} {bnd} :\n    {stmt} := by\n  have e := {call}\n"
                        f"  simp only [NF] at e ⊢\n  exact e\n")
            coll_alts.append(f"  | {p}, {g}, {pat} => some ({C}, {a2}, {G2}, {jn})")
            coll_leaves.setdefault((p, g), []).append((x['segs'], isinstance(tail, Ctx)))
            coll_inv.append((C, jn))
            nargs = len(vs) + (1 if isinstance(tail, Ctx) else 0) + 1
            coll_pf.append(f"  · simp only [Option.some.injEq, Prod.mk.injEq] at h\n    obtain ⟨rfl, rfl, rfl, rfl⟩ := h\n"
                           f"    exact ⟨_, by omega, xq_{rid} {' '.join(['_'] * nargs)}⟩")
        elif hk[0] == 'anu':
            X = s['items'][0][1]
            if [str(i[1]) for i in s['items'][1:]] != ['1']:
                raise PErr("anu start word")
            cpat = Lin((X.k - 2) // 2, {v: a // 2 for v, a in X.c.items()})
            if 2 * cpat + 2 != X:
                raise PErr("anu block")
            it = e['items']
            if it[0] != ('v', Lin(2)) or it[-1][0] != 'v':
                raise PErr(f"anu end word {it}")
            W2 = f"{ln(it[-1][1])} :: ({word_expr(it[1:-1])} ++ [2])"
            bnd = binders(vs, (" (S : List Sg)" if isinstance(tail, Ctx) else "") + " (x : Nat)" +
                          f" (hx : x = {X.lean()})")
            stmt = f"steps ({N}) (qr [1, x] 1 (flat ({pat}))) = some (qr ({W2}) {a2} ({G2}))"
            qlem.append(f"theorem xq_{rid} {bnd} :\n    {stmt} := by\n  subst hx\n  have e := {call}\n"
                        f"  simp only [NF] at e ⊢\n  exact e\n")
            cp = cpat.lean() if cpat.is_const() or len(cpat.c) == 1 else None
            anu_alts.append(f"  | {cp}, {pat} => some ⟨{W2}, {a2}, {G2}⟩")
            if cp != "c":
                raise PErr("anu with a split block")
            anu_leaves.append((x['segs'], isinstance(tail, Ctx)))
            nargs = len(vs) + (1 if isinstance(tail, Ctx) else 0) + 1
            anu_pf.append(f"  · cases h\n    exact ⟨_, by omega, xq_{rid} {' '.join(['_'] * nargs)} (by omega)⟩")
        else:
            X = s['items'][1][1]
            A = s['a']
            if s['items'][0][1] != Lin(1) or e['items'][0][1] != Lin(3):
                raise PErr("inner junction")
            C = word_expr(e['items'][1:])
            tag = ("0" if X.is_const() else "1") + ("0" if A.is_const() else "1")
            bnd = binders(vs, " (G : List Nat) (L : Tape) (x : Nat)" + f" (hx : x = {X.lean()})" +
                          f" (A : Nat) (hA : A = {A.lean()})")
            stmt = f"steps ({N}) (qx A [x] (rep 1 [true] L) G) = some (qx {a2} ({C}) (rep 3 [true] L) ({G2}))"
            qlem.append(f"theorem xq_inner{tag} {bnd} :\n    {stmt} := by\n  subst hx hA\n  have e := {call}\n"
                        f"  simp only [NF] at e ⊢\n  exact e\n")
            inner[tag] = (X, A, C, G2)
    if sorted(inner) != ['00', '01', '10', '11']:
        sys.exit(f"inner anomaly cases {sorted(inner)}")
    for w in [(0, 0, 1), (0, 0, 0, 0, 0, 1), (1, 0), (1, 1, 1, 1, 1, 0), (1, 1, 1), (0, 0, 0), (1, 1), (0, 1)]:
        words.add(w)
    lem, names = nf_lemmas(words)
    muls = set()
    for x in lv:
        for c in (x['leaf'].start, x['leaf'].end):
            for t in list(c.left) + list(c.right):
                if isinstance(t, Rep):
                    muls |= set(t.n.c.values())
        for it in x['end']['items'] + x['end']['gaps']:
            for v in ([it[1]] if it[0] == 'v' else it[1] + [it[2]]):
                muls |= set(v.c.values())
    for k in sorted(muls - {1, 2, 3}):
        ww = " ++ ".join(["w"] * k)
        lem.append(f"theorem rep_mul{k} (s : Nat) (w : List Bool) (X : Tape) : rep ({k} * s) w X = rep s ({ww}) X := by\n"
                   f"  induction s with\n  | zero => rfl\n  | succ s ih =>\n"
                   f"    rw [show {k} * (s + 1) = {k} * s{' + 1' * k} by omega{', rep_succ' * k}, ih, rep_succ{', app_app' * (k - 1)}]\n")
        names.append(f"rep_mul{k}")
    nf = NF_BASE + ", " + ", ".join(names)
    xr = rules_file("Machine", ns, rules,
                    f"The irregular Q-steps of {m} that its `astep` (Full.lean) leaves out, one tape rule per case of "
                    "the symbolic case split of `py/xleaves.py`.  Generated by `py/gen_xmap.py` in the folder of "
                    "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---; do not edit by hand.")
    open(os.path.join(d, "XRules.lean"), "w").write(xr)
    tpl = open(os.path.join(HERE, "XMap.lean.in")).read()
    gen = []
    gen.append("\n".join(lem))
    gen.append("\n".join(q.replace("[NF]", f"[{nf}]") for q in qlem))
    gen.append("/-- The collisions: `t = 2s + p` gaps of 2, the misaligned gap `g`, then the gaps `flat S`.  The "
               "answer is the blocks added in front of the word (last first), the new counter low part, the new gaps "
               "and how much the word's last block grows. -/\n"
               "def xcoll (s : Nat) : Nat → Nat → List Sg → Option (List Nat × Nat × List Nat × Nat)\n" +
               "\n".join(coll_alts) + "\n  | _, _, _ => none\n")
    gen.append("theorem xcoll_sound (s p g : Nat) (S : List Sg) {C : List Nat} {a' : Nat} {G' : List Nat} {j : Nat}\n"
               "    (h : xcoll s p g S = some (C, a', G', j)) (L : Tape) :\n"
               "    ∃ n, 1 ≤ n ∧ steps n (zc L (List.replicate (2 * s + p) 2 ++ g :: flat S)) = "
               "some (qx a' C (rep j [true] L) G') := by\n  unfold xcoll at h\n  split at h\n" +
               "\n".join(coll_pf) + "\n  · cases h\n")
    gen.append("/-- The anomaly with a one-unit counter: word `[1, 2c+2]`, counter low part 1, gaps `flat S`. -/\n"
               "def xanu : Nat → List Sg → Option AC\n" + "\n".join(anu_alts) + "\n  | _, _ => none\n")
    gen.append("theorem xanu_sound (c : Nat) (S : List Sg) {c' : AC} (h : xanu c S = some c') :\n"
               "    ∃ n, 1 ≤ n ∧ steps n (qr [1, 2 * c + 2] 1 (flat S)) = some c'.enc := by\n"
               "  unfold xanu at h\n  split at h\n" + "\n".join(anu_pf) + "\n  · cases h\n")
    out = tpl.replace("@@NS@@", ns).replace("@@M@@", m).replace("@@GEN@@", "\n".join(gen)).replace("@@NF@@", nf)
    open(os.path.join(d, "XMap.lean"), "w").write(out)
    race = open(os.path.join(HERE, "XRace.lean.in")).read()
    rg = []
    rg.append(total_thm("xcoll_total", "(s p g : Nat) (S : List Sg)", "p < 2 → g ≤ 1 → okS S = true → "
                        "(xcoll s p g S).isSome = true", coll_leaves))
    rg.append(total_thm("xanu_total", "(c : Nat) (S : List Sg)", "okS S = true → (xanu c S).isSome = true",
                        {None: anu_leaves}))
    pf = []
    for C, jn in coll_inv:
        hd = "all_goals trivial" if C == "[]" else ("refine ⟨by omega, ?_⟩\n      intro b hb\n      simp only [" + MEM +
                                          "] at hb\n      all_goals omega")
        pf.append("  · simp only [Option.some.injEq, Prod.mk.injEq] at h\n    obtain ⟨rfl, rfl, rfl, rfl⟩ := h\n"
                  f"    refine ⟨by omega, ?_, by decide, ?_⟩\n    · simp only [hd1]\n      {hd}\n    · {NMIS}")
    rg.append("theorem xcoll_inv (s p g : Nat) (S : List Sg) {C : List Nat} {a' : Nat} {G' : List Nat} {j : Nat}\n"
              "    (h : xcoll s p g S = some (C, a', G', j)) :\n"
              "    1 ≤ a' ∧ hd1 C ∧ j % 2 = 0 ∧ nmis G' ≤ 1 + nmis (flat S) := by\n  unfold xcoll at h\n  split at h\n" +
              "\n".join(pf) + "\n  · cases h\n")
    pf = []
    for _ in anu_leaves:
        pf.append("  · cases h\n    refine ⟨goodH_last2 _ _ (by omega) ?_, by (try dsimp only); omega, ?_⟩\n    · intro b hb\n"
                  f"      simp only [{MEM}] at hb\n      all_goals omega\n    · {NMIS}")
    rg.append("theorem xanu_inv (c : Nat) (S : List Sg) {c' : AC} (h : xanu c S = some c') :\n"
              "    goodH c'.W ∧ 1 ≤ c'.a ∧ nmis c'.G ≤ 1 + nmis (flat S) := by\n  unfold xanu at h\n  split at h\n" +
              "\n".join(pf) + "\n  · cases h\n")
    out = race.replace("@@NS@@", ns).replace("@@M@@", m).replace("@@GEN@@", "\n".join(rg))
    open(os.path.join(d, "XRace.lean"), "w").write(out)
    print(f"{m}: {len(rules)} rules ({counters})")


if __name__ == "__main__":
    main()
