"""Write lean/XRules.lean, lean/XMap.lean and lean/XRace.lean for 1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---, the
sister machine whose collisions read the end of the word and which keeps two misaligned gaps at a time.  The same
pipeline as `gen_xmap.py`, with the case split of `xleaves2.py`:

* XRules.lean: one tape rule per case, proved by `bbtools.symtm.prove`.
* XMap.lean (template XMap2.lean.in): the rules restated on word-and-counter configurations, one decision function
  per group of cases (`xg..` collisions, `xz..` collisions with a second gap 0, `xanu`), the dispatcher `xc`, and
  `bstep` with `bstep_sound` and `not_halts_of_brun`.
* XRace.lean (template XRace2.lean.in): the invariant allows two misaligned gaps; `xc` is total outside four
  halting patterns (`hz`) and keeps the invariant.

usage (from the repository root):
  python3 holdouts/1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---/py/gen_xmap2.py 1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---
"""
import collections
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file, Rep, Ctx, Blank, Lin, Config  # noqa: E402
from xleaves import word_expr, gap_expr, ln, PErr, subst_cfg, parse_q  # noqa: E402
from xleaves2 import leaves2, segs_of2, word_start, peel  # noqa: E402
from gen_xmap import nf_lemmas, rep_words, NF_BASE, MEM, NMIS  # noqa: E402

TAGS = {('ctx', ('1', '2*n+1')): 'A', ('blank', ('1', '2*n+2')): 'B', ('ctx', ('3',)): 'C',
        ('ctx', ('2*n+5',)): 'D', ('blank', ('2',)): 'E', ('blank', ('2*n+4',)): 'F'}
WPRE = {'A': "[1, 2 * n + 1]", 'B': "[1, 2 * n + 2]", 'C': "[3]", 'D': "[2 * n + 5]", 'E': "[2]", 'F': "[2 * n + 4]"}
BLANKT = {'B', 'E', 'F'}


def binders(vs, extra=""):
    return (f"({' '.join(vs)} : Nat)" if vs else "") + extra


def seg_pat2(segs, tail):
    e = "S" if isinstance(tail, Ctx) else "[]"
    for kind, n in reversed(segs):
        e = f".{kind} {ln(n)} :: {e}"
    return e


def rename(lf_start, lf_end, old, new):
    v = Lin(0, {new: 1})
    return subst_cfg(lf_start, old, v), subst_cfg(lf_end, old, v)


# ---------------------------------------------------------------- leaves into groups
def prep(hk, start, end):
    """Parse a leaf (start, end configs) into the data of one case; None if it needs a split first (raises)."""
    s, e = parse_q(start), parse_q(peel(end))
    d = dict(head=hk, start_cfg=start, end_cfg=end, start=s, end=e)
    if hk[0] in ('coll', 'collz'):
        p, g = hk[1], hk[2]
        gi = s['gaps']
        T, k = Lin(0), 0
        while not (gi[k][0] == 'v' and gi[k][1] == Lin(g)):
            it = gi[k]
            if it[0] == 'g' and all(str(b) == '2' for b in it[1]):
                T = T + len(it[1]) * it[2]
            elif it[0] == 'v' and it[1] == Lin(2):
                T = T + 1
            else:
                raise PErr(f"coll gaps {gi}")
            k += 1
        s2 = T - p
        d['s'] = Lin(s2.k // 2, {x: c // 2 for x, c in s2.c.items()})
        if 2 * d['s'] + p != T:
            raise PErr(f"coll count {T}")
        gi = gi[k + 1:]
        if hk[0] == 'collz':
            T, k = Lin(0), 0
            while not (gi[k][0] == 'v' and gi[k][1] == Lin(0)):
                it = gi[k]
                if it[0] == 'g' and all(str(b) == '2' for b in it[1]):
                    T = T + len(it[1]) * it[2]
                elif it[0] == 'v' and it[1] == Lin(2):
                    T = T + 1
                else:
                    raise PErr(f"collz gaps {gi}")
                k += 1
            v2 = T - hk[3]
            d['v'] = Lin(v2.k // 2, {x: c // 2 for x, c in v2.c.items()})
            if 2 * d['v'] + hk[3] != T:
                raise PErr(f"collz count {T}")
            gi = gi[k + 1:]
        d['segs'] = segs_of2(gi)
        d['word'] = word_start(start)
    elif hk[0] == 'anu':
        d['segs'] = segs_of2(s['gaps'])
    else:
        d['segs'] = []
    return d


def word_tag(d):
    """Rename the word's parameter to n; the view tag."""
    w = d.get('word')
    if w is None:
        return d, None
    anchor, blocks = w
    vs = sorted(set().union(*[b.vars() for b in blocks]))
    if len(vs) > 1:
        raise PErr(f"word {blocks}")
    if vs:
        st, en = rename(d['start_cfg'], d['end_cfg'], vs[0], 'n')
        d = prep(d['head'], st, en)
        anchor, blocks = d['word']
    key = ('blank' if isinstance(anchor, Blank) else 'ctx', tuple(str(b).replace(' ', '') for b in blocks))
    if key not in TAGS:
        raise PErr(f"word view {key}")
    return d, TAGS[key]


def path_of(d):
    """The path of a case in its group's trie: ('nat', v) for collz, then the segments, then the end marker."""
    out = []
    if d['head'][0] in ('coll', 'collz'):
        out.append(('nat', d['s']))
    if d['head'][0] == 'collz':
        out.append(('nat', d['v']))
    out += list(d['segs'])
    tail = d['start']['tail']
    out.append(('S',) if isinstance(tail, Ctx) else ('end',))
    return out


def norm(el):
    """A path element with the name of its count variable left out."""
    if len(el) < 2:
        return el
    n = el[1]
    if n.is_const():
        return (el[0], str(n.k))
    if el[0] == 'big':
        return (el[0], 'q')
    return (el[0], f"_+{n.k}")


def split_conflicts(cases):
    """Where cases of a group meet a count in different forms (constants and `x + lo` with different lo), replace
    each `x + lo` by the constants up to the largest lo and `x + lomax` (instances of the same rule)."""
    changed = True
    while changed:
        changed = False
        nodes = collections.defaultdict(list)
        consts = collections.defaultdict(set)
        for i, c in enumerate(cases):
            pth = c['path']
            for depth in range(len(pth)):
                el = pth[depth]
                if len(el) == 2 and el[0] != 'big':
                    key = (tuple(map(norm, pth[:depth])), el[0])
                    if el[1].is_const():
                        consts[key].add(el[1].k)
                    else:
                        nodes[key].append((i, depth))
        for key, occ in nodes.items():
            los = {cases[i]['path'][dp][1].k for i, dp in occ}
            lomax = max([max(los)] + [k + 1 for k in consts[key] if k >= min(los)])
            if all(lo == lomax for lo in los):
                continue
            new = []
            done = set()
            for i, dp in occ:
                if i in done:
                    continue
                done.add(i)
                el = cases[i]['path'][dp][1]
                if el.k == lomax:
                    continue
                (x,) = el.vars()
                c = cases[i]
                for k in range(el.k, lomax):
                    st, en = subst_cfg(c['d']['start_cfg'], x, Lin(k - el.k)), subst_cfg(c['d']['end_cfg'], x, Lin(k - el.k))
                    new.append((i, st, en))
                st, en = subst_cfg(c['d']['start_cfg'], x, Lin(lomax - el.k, {x: 1})), subst_cfg(c['d']['end_cfg'], x, Lin(lomax - el.k, {x: 1}))
                new.append((i, st, en))
            if new:
                drop = {i for i, _, _ in new}
                keep = [c for j, c in enumerate(cases) if j not in drop]
                for i, st, en in new:
                    c = cases[i]
                    keep.append(mk_case(c['d']['head'], st, en, c.get('halt', False)))
                cases[:] = keep
                changed = True
                break
    return cases


def prune(cases):
    """Drop the cases that a case with an untouched context at a shorter path already covers."""
    general = set()
    for c in cases:
        if c['path'][-1] == ('S',):
            general.add(tuple(map(norm, c['path'][:-1])))
    out = []
    for c in cases:
        pn = tuple(map(norm, c['path'][:-1]))
        if any(pn[:k] in general for k in range(len(pn))) or (pn in general and c['path'][-1] != ('S',)):
            continue
        out.append(c)
    # two cases with the same general path: keep one
    seen, res = set(), []
    for c in out:
        key = tuple(map(norm, c['path']))
        if key in seen:
            continue
        seen.add(key)
        res.append(c)
    return res


def mk_case(hk, st, en, halt=False):
    if halt:
        p = [('nat', Lin(0, {'s': 1})), ('nat', halt_v(hk, st)), ('S',)]
        return dict(d=dict(head=hk, start_cfg=st, end_cfg=en), path=p, halt=True)
    d = prep(hk, st, en)
    d, tag = word_tag(d)
    return dict(d=d, path=path_of(d), tag=tag)


def halt_v(hk, st):
    """The count v of a halting collz case (a constant)."""
    for t in st.right:
        if isinstance(t, Rep) and t.word == (0, 0, 1, 0, 0, 1) and not str(t.n) == 's':
            pass
    txt = str(st)
    m = re.search(r"\(001001\)\^(\d+)", txt.split('A>')[1].split('(001001)^s', 1)[1])
    if not m:
        raise PErr(f"halting case {txt}")
    return Lin(int(m.group(1)))


# ---------------------------------------------------------------- totality from the trie
def build_trie(cases):
    root = {}
    for c in cases:
        node = root
        for el in c['path'][:-1]:
            ex = [k for k in node if k[:2] == norm(el)]
            node = node[ex[0]] if ex else node.setdefault(norm(el) + (el[1],), {})
        node[c['path'][-1] + (('halt',) if c.get('halt') else ())] = None
    return root


def alts(node, prefix, prev, zsroot, out):
    """(pattern elements, kind) with kind 'leaf', 'halt' or the reason a pattern cannot occur."""
    keys = list(node)
    ends = [k for k in keys if k[0] in ('S', 'end')]
    if any(k[0] == 'S' for k in ends):
        if len(keys) != 1:
            raise PErr(f"wildcard with siblings at {prefix}")
        out.append((prefix + ["S"], 'halt' if keys[0][-1] == 'halt' else 'leaf'))
        return
    natk = [k for k in keys if k[0] == 'nat']
    if natk:
        consts = sorted(k[2].k for k in natk if k[2].is_const())
        var = [k for k in natk if not k[2].is_const()]
        if len(var) != 1:
            raise PErr(f"nat forms {[k[1] for k in natk]}")
        lo = var[0][2].k
        if sorted(set(consts)) != list(range(lo)):
            raise PErr(f"nat consts {consts} lo {lo}")
        for k in natk:
            alts(node[k], prefix + [ln(k[2])], None, zsroot, out)
        return
    if ('end',) in keys:
        out.append((prefix + ["[]"], 'leaf'))
    else:
        raise PErr(f"no blank-tape case at {prefix}")
    for kind in ('two', 'five', 'big', 'm0', 'm1'):
        ks = [k for k in keys if k[0] == kind]
        if not ks:
            if kind == prev and kind in ('two', 'five'):
                out.append((prefix + [f".{kind} _", "_"], 'ok'))
            elif kind in ('m0', 'm1'):
                out.append((prefix + [f".{kind} _", "_"], 'nmis'))
            else:
                raise PErr(f"no {kind} case at {prefix}")
            continue
        if kind == prev and kind in ('two', 'five'):
            raise PErr(f"{kind} after {kind} at {prefix}")
        if kind == 'big':
            for k in ks:
                if not (len(k[2].c) == 1 and k[2].k == 0):
                    raise PErr(f"split big gap at {prefix}")
                alts(node[k], prefix + [f".big {ln(k[2])}"], kind, zsroot, out)
            continue
        consts = sorted(k[2].k for k in ks if k[2].is_const())
        var = [k for k in ks if not k[2].is_const()]
        if len(var) != 1:
            raise PErr(f"{kind} counts at {prefix}: {[k[1] for k in ks]}")
        lo = var[0][2].k
        for c in range(lo):
            if c not in consts:
                if c == 0 and kind in ('two', 'five'):
                    out.append((prefix + [f".{kind} 0", "_"], 'ok'))
                elif c == 0 and kind == 'm0' and zsroot and (prev is None or prev == 'two'):
                    out.append((prefix + [".m0 0", "_"], 'zs'))
                else:
                    raise PErr(f"{kind} count {c} missing at {prefix}")
        for k in ks:
            alts(node[k], prefix + [f".{kind} {ln(k[2])}"], kind, zsroot and kind == 'two' and prev is None, out)


FIN = ("first\n  | exact e\n  | (simp only [← rep_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at e ⊢; exact e)")
HB = ""

CLOSE = {
    'ok': "by simp [okS, notTwo, notFive] at h1",
    'zs': "by simp [zs] at h3",
    'hz': "by simp [hz] at h3",
    'nmis': ("by\n    simp only [flat, Sg.gs, nmis_append, nmis, nmis_rep, List.cons_append, List.nil_append,\n"
             "      List.singleton_append, List.append_assoc] at h2\n    repeat' split at h2\n    all_goals omega"),
}


def total_thm(name, fname, gk, hyps, cases):
    """`∀ args S, okS S → hyp2 → hyp3 → (f args S).isSome`, by one alternative per path of the trie.  `gk`: 'c'
    (args s S), 'w' (s n S) or 'z' (s v S)."""
    out = []
    alts(build_trie(cases), [], None, gk != 'z', out)
    lines = []
    nn = 2 if gk == 'z' else 1
    for pat, kind in out:
        nats, segs = pat[:nn], " :: ".join(pat[nn:])
        pp = ", ".join(nats[:1] + (["_"] if gk == 'w' else []) + nats[1:] + [segs])
        if kind == 'leaf':
            lines.append(f"  | {pp}, _, _, _ => rfl")
        elif kind == 'halt':
            lines.append(f"  | {pp}, _, _, h3 => {CLOSE['hz']}")
        else:
            lines.append(f"  | {pp}, h1, h2, h3 => {CLOSE[kind]}")
    args = {'c': "(s : Nat)", 'w': "(s n : Nat)", 'z': "(s v : Nat)"}[gk]
    callargs = {'c': "s", 'w': "s n", 'z': "s v"}[gk]
    return (HB + f"theorem {name} : ∀ {args} (S : List Sg), okS S = true → {hyps[0]} → {hyps[1]} → "
            f"({fname} {callargs} S).isSome = true\n" + "\n".join(lines) + "\n")


# ---------------------------------------------------------------- main
def main():
    m = sys.argv[1]
    d0 = os.path.join(HERE, "../../", m, "lean")
    ns = re.search(r"^namespace (\w+)", open(os.path.join(d0, "Machine.lean")).read(), re.M).group(1)
    groups = collections.defaultdict(list)
    anu, inner = [], {}
    for x in leaves2(m):
        hk = x['head']
        if x['kind'] == 'halt':
            if hk[0] != 'collz':
                sys.exit(f"halting case outside collz: {hk}")
            c = mk_case(hk, x['leaf'].start, None, halt=True)
            groups[('z', hk[1], hk[2], hk[3])].append(c)
            continue
        if x['kind'] != 'rule':
            sys.exit(f"not a rule: {hk} {x['leaf']}")
        c = mk_case(hk, x['leaf'].start, x['leaf'].end)
        if hk[0] == 'coll':
            key = ('c', hk[1], hk[2]) + ((c['tag'],) if c['tag'] else ())
            if (hk[2] == 1) != bool(c['tag']):
                sys.exit(f"word use in {hk}")
            groups[key].append(c)
        elif hk[0] == 'collz':
            if c['tag']:
                sys.exit("collz reads the word")
            groups[('z', hk[1], hk[2], hk[3])].append(c)
        elif hk[0] == 'anu':
            anu.append(c)
        else:
            inner.setdefault('all', []).append(c)
    for k in list(groups):
        groups[k] = prune(split_conflicts(groups[k]))
    expect = {('c', p, 0) for p in (0, 1)} | {('c', p, 1, t) for p in (0, 1) for t in 'ABCDEF'} | \
        {('z', p, g, r) for p in (0, 1) for g in (0, 1) for r in (0, 1)}
    if set(groups) != expect:
        sys.exit(f"groups {sorted(set(groups) ^ expect)}")

    rules, qlem, words = [], [], set()
    defs, sounds, totals, invs = [], [], [], []
    hzs = []
    counter = collections.Counter()

    def gname(key):
        if key[0] == 'c':
            return f"xg{key[1]}{key[2]}" + (key[3] if len(key) > 3 else "")
        return f"xz{key[1]}{key[2]}{key[3]}"

    for key in sorted(groups, key=str):
        fname = gname(key)
        cs = groups[key]
        tag = key[3] if key[0] == 'c' and len(key) > 3 else None
        blank = tag in BLANKT
        p, g = key[1], key[2]
        arms, pfs, ipfs = [], [], []
        for c in cs:
            if c.get('halt'):
                hzs.append(f"  | {p}, {g}, {key[3]}, {ln(c['path'][0][1])} => true")
                continue
            d = c['d']
            st, en = d['start_cfg'], d['end_cfg']
            k = counter[fname]
            counter[fname] += 1
            rid = f"{fname}_{k}"
            txt, fin = prove(m, "xr_" + rid, st, en, count_first=True, max_seg=40, rotate=True,
                             doc=f"case {rid} of the irregular steps (found by xleaves2.py)")
            rules.append(txt)
            for w in list(rep_words(st)) + list(rep_words(fin)):
                words.add(w)
            N = fin.steps.lean()
            vs = sorted(st.vars() | en.vars())
            s_, e_ = d['start'], d['end']
            tail = s_['tail']
            it = e_['items']
            j = it[0]
            if j[0] != 'v':
                raise PErr(f"junction {j}")
            jn = ln(j[1])
            C = word_expr(it[1:])
            a2 = ln(e_['a'])
            G2 = gap_expr(e_['gaps'], "flat S" if isinstance(e_['tail'], Ctx) else "[]")
            pat = seg_pat2(d['segs'], tail)
            ctx_args = []
            if isinstance(st.left[0], Ctx):
                ctx_args.append(f"({st.left[0].name} := L)")
            if isinstance(tail, Ctx):
                ctx_args.append(f"({tail.name} := gl (flat S))")
            call = f"xr_{rid} " + " ".join(f"({v} := {v})" for v in vs) + " " + " ".join(ctx_args)
            if tag:
                wp = "[" + ", ".join(ln(b) for b in d['word'][1]) + "]"
                if wp.replace("(", "").replace(")", "") != WPRE[tag]:
                    raise PErr(f"word {wp} vs {WPRE[tag]}")
                wpre = WPRE[tag]
            else:
                wpre = None
            Lt = "blank" if blank else "L"
            zcL = f"(wlx {wpre} {Lt})" if wpre else "L"
            if key[0] == 'z':
                gaps = f"List.replicate (2 * {ln(d['s'])} + {p}) 2 ++ {g} :: (List.replicate (2 * {ln(d['v'])} + {key[3]}) 2 ++ 0 :: flat ({pat}))"
            else:
                gaps = f"List.replicate (2 * {ln(d['s'])} + {p}) 2 ++ {g} :: flat ({pat})"
            bnd = binders(vs, (" (S : List Sg)" if isinstance(tail, Ctx) else "") + ("" if blank else " (L : Tape)"))
            stmt = f"steps ({N}) (zc {zcL} ({gaps})) = some (qx {a2} ({C}) (rep {jn} [true] {Lt}) ({G2}))"
            qlem.append(f"theorem xq_{rid} {bnd} :\n    {stmt} := by\n  have e := {call}\n"
                        f"  simp only [NF] at e ⊢\n  {FIN}\n")
            sp = ln(d['s'])
            if key[0] == 'z':
                arms.append(f"  | {sp}, {ln(d['v'])}, {pat} => some ({C}, {a2}, {G2}, {jn})")
            elif tag:
                arms.append(f"  | {sp}, n, {pat} => some ({C}, {a2}, {G2}, {jn})")
            else:
                arms.append(f"  | {sp}, {pat} => some ({C}, {a2}, {G2}, {jn})")
            nargs = len(vs) + (1 if isinstance(tail, Ctx) else 0) + (0 if blank else 1)
            pfs.append(f"  · simp only [Option.some.injEq, Prod.mk.injEq] at h\n    obtain ⟨rfl, rfl, rfl, rfl⟩ := h\n"
                       f"    exact ⟨_, by omega, xq_{rid} {' '.join(['_'] * nargs)}⟩")
            hd = ("all_goals first\n        | trivial\n        | (refine ⟨by omega, ?_⟩\n           intro b hb\n"
                  "           (try simp only [" + MEM + "] at hb)\n           all_goals omega)")
            ipfs.append("  · simp only [Option.some.injEq, Prod.mk.injEq] at h\n    obtain ⟨rfl, rfl, rfl, rfl⟩ := h\n"
                        f"    refine ⟨by omega, ?_, by omega, by {'omega' if blank else 'trivial'}, ?_⟩\n"
                        f"    · simp only [hd1, List.replicate_succ, List.cons_append, List.nil_append, List.append_nil]\n      {hd}\n    · {NMIS}")
        # definition
        if key[0] == 'z':
            sig = f"def {fname} : Nat → Nat → List Sg → Option Res"
            wild = "  | _, _, _ => none"
            hyp = "(h : " + fname + " s v S = some (C, a', G', j))"
            fargs = "(s v : Nat)"
        else:
            sig = f"def {fname} : Nat → Nat → List Sg → Option Res" if tag else f"def {fname} : Nat → List Sg → Option Res"
            wild = "  | _, _, _ => none" if tag else "  | _, _ => none"
            hyp = "(h : " + fname + (" s n" if tag else " s") + " S = some (C, a', G', j))"
            fargs = "(s n : Nat)" if tag else "(s : Nat)"
        defs.append(f"/-- Cases of group {key}. -/\n{sig}\n" + "\n".join(arms) + "\n" + wild + "\n")
        if key[0] == 'z':
            gaps = f"List.replicate (2 * s + {p}) 2 ++ {g} :: (List.replicate (2 * v + {key[3]}) 2 ++ 0 :: flat S)"
        else:
            gaps = f"List.replicate (2 * s + {p}) 2 ++ {g} :: flat S"
        Lt = "blank" if blank else "L"
        zcL = f"(wlx {WPRE[tag]} {Lt})" if tag else "L"
        sounds.append(HB + f"theorem {fname}_sound {fargs} (S : List Sg) {{C : List Nat}} {{a' : Nat}} {{G' : List Nat}} "
                      f"{{j : Nat}}\n    {hyp}" + ("" if blank else " (L : Tape)") +
                      f" :\n    ∃ k, 1 ≤ k ∧ steps k (zc {zcL} ({gaps})) = some (qx a' C (rep j [true] {Lt}) G') := by\n"
                      f"  unfold {fname} at h\n  split at h\n" + "\n".join(pfs) + "\n  · cases h\n")
        bound = "2" if key[0] == 'z' else "1"
        invs.append(HB + f"theorem {fname}_inv {fargs} (S : List Sg) {{C : List Nat}} {{a' : Nat}} {{G' : List Nat}} "
                    f"{{j : Nat}}\n    {hyp} :\n    1 ≤ a' ∧ hd1 C ∧ j % 2 = 0 ∧ {'2 ≤ j' if blank else 'True'} ∧ "
                    f"nmis G' ≤ {bound} + nmis (flat S) := by\n  unfold {fname} at h\n  split at h\n" +
                    "\n".join(ipfs) + "\n  · cases h\n")
        if key[0] == 'z':
            totals.append(total_thm(f"{fname}_total", fname, 'z',
                                    ("nmis (flat S) = 0", f"hz {p} {g} {key[3]} v = false"), cs))
        else:
            totals.append(total_thm(f"{fname}_total", fname, 'w' if tag else 'c',
                                    ("nmis (flat S) ≤ 1", "zs S = none"), cs))
    # anomaly with a one-unit counter and the anomaly inside the word: as in gen_xmap.py
    anu_alts, anu_pf, anu_ipf, anu_cases = [], [], [], []
    for k, c in enumerate(anu):
        d = c['d']
        st, en = d['start_cfg'], d['end_cfg']
        rid = f"u_{k}"
        txt, fin = prove(m, "xr_" + rid, st, en, count_first=True, max_seg=40, rotate=True,
                         doc=f"case {rid} of the irregular steps (found by xleaves2.py)")
        rules.append(txt)
        for w in list(rep_words(st)) + list(rep_words(fin)):
            words.add(w)
        N = fin.steps.lean()
        vs = sorted(st.vars() | en.vars())
        s_, e_ = d['start'], d['end']
        tail = s_['tail']
        X = s_['items'][0][1]
        cpat = Lin((X.k - 2) // 2, {v: a // 2 for v, a in X.c.items()})
        if 2 * cpat + 2 != X:
            raise PErr(f"anu block {X}")
        c['path'] = [('nat', cpat)] + c['path']
        it = e_['items']
        single = len(it) == 1
        if single:
            W2 = f"[{ln(it[0][1])}]"
        elif it[0] != ('v', Lin(2)):
            raise PErr(f"anu end word {it}")
        else:
            W2 = f"{ln(it[-1][1])} :: ({word_expr(it[1:-1])} ++ [2])"
        a2 = ln(e_['a'])
        G2 = gap_expr(e_['gaps'], "flat S" if isinstance(e_['tail'], Ctx) else "[]")
        pat = seg_pat2(d['segs'], tail)
        ctx_args = [f"({tail.name} := gl (flat S))"] if isinstance(tail, Ctx) else []
        call = f"xr_{rid} " + " ".join(f"({v} := {v})" for v in vs) + " " + " ".join(ctx_args)
        bnd = binders(vs, (" (S : List Sg)" if isinstance(tail, Ctx) else "") + f" (x : Nat) (hx : x = {X.lean()})")
        qlem.append(f"theorem xq_{rid} {bnd} :\n    steps ({N}) (qr [1, x] 1 (flat ({pat}))) = some (qr ({W2}) {a2} ({G2})) := by\n"
                    f"  subst hx\n  have e := {call}\n  simp only [NF] at e ⊢\n  {FIN}\n")
        anu_alts.append(f"  | {ln(cpat)}, {pat} => some ⟨{W2}, {a2}, {G2}⟩")
        nargs = len(vs) + (1 if isinstance(tail, Ctx) else 0) + 1
        anu_pf.append(f"  · cases h\n    exact ⟨_, by omega, xq_{rid} {' '.join(['_'] * nargs)} (by omega)⟩")
        if single:
            anu_ipf.append("  · cases h\n    refine ⟨⟨rfl, by decide⟩, by (try dsimp only); omega, ?_⟩\n"
                           f"    · {NMIS}")
        else:
            anu_ipf.append("  · cases h\n    refine ⟨goodH_last2 _ _ (by omega) ?_, by (try dsimp only); omega, ?_⟩\n    · intro b hb\n"
                           f"      simp only [{MEM}] at hb\n      all_goals omega\n    · {NMIS}")
        anu_cases.append(c)
    defs.append("/-- The anomaly with a one-unit counter: word `[1, 2c+2]`, counter low part 1, gaps `flat S`. -/\n"
                "def xanu : Nat → List Sg → Option AC\n" + "\n".join(anu_alts) + "\n  | _, _ => none\n")
    sounds.append("theorem xanu_sound (c : Nat) (S : List Sg) {c' : AC} (h : xanu c S = some c') :\n"
                  "    ∃ n, 1 ≤ n ∧ steps n (qr [1, 2 * c + 2] 1 (flat S)) = some c'.enc := by\n"
                  "  unfold xanu at h\n  split at h\n" + "\n".join(anu_pf) + "\n  · cases h\n")
    totals.append("theorem xanu_inv (c : Nat) (S : List Sg) {c' : AC} (h : xanu c S = some c') :\n"
                "    goodH c'.W ∧ 1 ≤ c'.a ∧ nmis c'.G ≤ 1 + nmis (flat S) := by\n  unfold xanu at h\n  split at h\n" +
                "\n".join(anu_ipf) + "\n  · cases h\n")
    tl = []
    alts_out = []
    alts(build_trie(anu_cases), [], None, False, alts_out)
    for pat, kind in alts_out:
        pp = pat[0] + ", " + " :: ".join(pat[1:])
        if kind == 'leaf':
            tl.append(f"  | {pp}, _, _ => rfl")
        elif kind in ('ok', 'nmis'):
            tl.append(f"  | {pp}, h1, h2 => {CLOSE[kind]}")
        else:
            raise PErr(f"anu alternative {kind}")
    totals.append("theorem xanu_total : ∀ (c : Nat) (S : List Sg), okS S = true → nmis (flat S) = 0 → "
                  "(xanu c S).isSome = true\n" + "\n".join(tl) + "\n")
    tags = {}
    for c in inner['all']:
        d = c['d']
        st, en = d['start_cfg'], d['end_cfg']
        s_, e_ = d['start'], d['end']
        X, A = s_['items'][1][1], s_['a']
        tg = ("0" if X.is_const() else "1") + ("0" if A.is_const() else "1")
        rid = f"i_{tg}"
        txt, fin = prove(m, "xr_" + rid, st, en, count_first=True, max_seg=40, rotate=True,
                         doc=f"case {rid} of the irregular steps (found by xleaves2.py)")
        rules.append(txt)
        for w in list(rep_words(st)) + list(rep_words(fin)):
            words.add(w)
        N = fin.steps.lean()
        vs = sorted(st.vars() | en.vars())
        if s_['items'][0][1] != Lin(1) or e_['items'][0][1] != Lin(3):
            raise PErr("inner junction")
        C = word_expr(e_['items'][1:])
        G2 = gap_expr(e_['gaps'], "G" if isinstance(e_['tail'], Ctx) else "[]")
        a2 = ln(e_['a'])
        ctx_args = [f"({st.left[0].name} := L)"]
        if isinstance(s_['tail'], Ctx):
            ctx_args.append(f"({s_['tail'].name} := gl G)")
        call = f"xr_{rid} " + " ".join(f"({v} := {v})" for v in vs) + " " + " ".join(ctx_args)
        bnd = binders(vs, f" (G : List Nat) (L : Tape) (x : Nat) (hx : x = {X.lean()}) (A : Nat) (hA : A = {A.lean()})")
        qlem.append(f"theorem xq_inner{tg} {bnd} :\n    steps ({N}) (qx A [x] (rep 1 [true] L) G) = some (qx {a2} ({C}) "
                    f"(rep 3 [true] L) ({G2})) := by\n  subst hx hA\n  have e := {call}\n  simp only [NF] at e ⊢\n  exact e\n")
        tags[tg] = 1
    if sorted(tags) != ['00', '01', '10', '11']:
        sys.exit(f"inner cases {sorted(tags)}")

    for w in [(0, 0, 1), (0, 0, 0, 0, 0, 1), (1, 0), (1, 1, 1, 1, 1, 0), (1, 1, 1), (0, 0, 0), (1, 1), (0, 1)]:
        words.add(w)
    lem, names = nf_lemmas(words)
    muls = set()
    for cs in list(groups.values()) + [anu, inner['all']]:
        for c in cs:
            if c.get('halt'):
                continue
            for cfg in (c['d']['start_cfg'], c['d']['end_cfg']):
                for t in list(cfg.left) + list(cfg.right):
                    if isinstance(t, Rep):
                        muls |= set(t.n.c.values())
            for it in c['d']['end']['items'] + c['d']['end']['gaps']:
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
                    "the symbolic case split of `py/xleaves2.py`.  Generated by `py/gen_xmap2.py` in the folder of "
                    "1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---; do not edit by hand.")
    open(os.path.join(d0, "XRules.lean"), "w").write(xr)
    gen = ["\n".join(lem), "\n".join(q.replace("[NF]", f"[{nf}]") for q in qlem), "\n".join(defs), "\n".join(sounds),
           "\n".join(invs)]
    tpl = open(os.path.join(HERE, "XMap2.lean.in")).read()
    out = tpl.replace("@@NS@@", ns).replace("@@M@@", m).replace("@@GEN@@", "\n".join(gen))
    open(os.path.join(d0, "XMap.lean"), "w").write(out)
    hz = "/-- The four halting patterns: a gap 0 right behind the colliding gap (`v` pairs and `r` gaps of 2 between). -/\n" \
         "def hz : Nat → Nat → Nat → Nat → Bool\n" + "\n".join(sorted(set(hzs))) + "\n  | _, _, _, _ => false\n"
    race = open(os.path.join(HERE, "XRace2.lean.in")).read()
    out = race.replace("@@NS@@", ns).replace("@@M@@", m).replace("@@HZ@@", hz).replace(
        "@@GEN@@", "\n".join(totals))
    open(os.path.join(d0, "XRace.lean"), "w").write(out)
    print(f"{m}: {len(rules)} rules, {len(hzs)} halting patterns, groups {dict(counter)}")


if __name__ == "__main__":
    main()
