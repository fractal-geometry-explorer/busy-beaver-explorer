"""Generate BB6/Rules.lean: every mark rule of proofs.py as a Lean theorem, with a proof that follows the Python
prover's own trace (single steps by `rfl`, the three cycle lemmas where it used them).

Tape terms.  A symtm configuration is  left-tokens  STATE>  right-tokens, tokens being cells 0/1, Rep(word, n),
Ctx(name) or Blank().  The Lean right stream lists cells in reading order: `cons`, `app`, `rep n word`.  The Lean
left stream lists cells nearest first, so a written word is reversed and a written Rep(word, n) becomes
`rep n (reversed word)`.

Where the Python prover applies PASS/SHIFT (on the right) or CARRY (on the left), the natural term may need
re-bracketing into `rep k [0,1] rest`: a cell x in front of (y x)^n is (x y)^n x (`rep_shift'`), and a repeat
absorbs a following copy of its word (`rep_cons2`).  The generator emits exactly those rewrites.

usage: python3 gen_rules.py > BB6/Rules.lean   (run from the directory containing rec/symtm.py and rec/proofs.py)
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'rec'))
from symtm import Lin, Rep, Ctx, Blank, step as sstep, try_lemma, Halted, count_pairs, tokens as toks
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'rec', 'proofs.py')).read().split("if __name__")[0]
exec(src)

B = {0: 'false', 1: 'true'}

def lin_lean(n):
    n = Lin(n) if not isinstance(n, Lin) else n
    parts = []
    for v, a in sorted(n.c.items()):
        parts.append(v if a == 1 else f'{a} * {v}')
    if n.k or not parts: parts.append(str(n.k))
    return ' + '.join(parts)

def word_lean(w): return '[' + ', '.join(B[x] for x in w) + ']'

def right_term(tks):
    """Lean term of a right-hand token list (reading order)."""
    acc = None
    for t in reversed(tks):
        if isinstance(t, Ctx): assert acc is None; acc = t.name
        elif isinstance(t, Blank): assert acc is None; acc = 'blank'
        elif isinstance(t, int): acc = f'cons {B[t]} ({acc})'
        elif isinstance(t, Rep):
            if t.n.is_zero(): continue
            acc = f'rep ({lin_lean(t.n)}) {word_lean(t.word)} ({acc})'
        else: raise ValueError(t)
    return acc

def left_term(tks):
    """Lean term of a left-hand token list (written left to right; result nearest first)."""
    acc = None
    for t in tks:
        if isinstance(t, Ctx): assert acc is None; acc = t.name
        elif isinstance(t, Blank): assert acc is None; acc = 'blank'
        elif isinstance(t, int): acc = f'cons {B[t]} ({acc})'
        elif isinstance(t, Rep):
            if t.n.is_zero(): continue
            acc = f'rep ({lin_lean(t.n)}) {word_lean(tuple(reversed(t.word)))} ({acc})'
        else: raise ValueError(t)
    return acc

def light(tks):
    """Expand repeats with a constant count into cells (a definitional unfolding); keep symbolic repeats."""
    out = []
    for t in tks:
        if isinstance(t, Rep) and t.n.is_const(): out.extend(list(t.word) * t.n.k)
        else: out.append(t)
    return out

def cfg_term(c): return f'⟨{left_term(light(c.left))}, {right_term(light(c.right))}, .{c.state}⟩'

def nearest_first(left_tokens):
    """The left tokens as a nearest-first token list, with Rep words reversed."""
    out = []
    for t in reversed(left_tokens):
        if isinstance(t, Rep): out.append(Rep(tuple(reversed(t.word)), t.n))
        else: out.append(t)
    return out

def to_lean_stream(nf):
    """Lean term of a nearest-first token list (the last token is the context)."""
    acc = None
    for t in reversed(nf):
        if isinstance(t, Ctx): acc = t.name
        elif isinstance(t, Blank): acc = 'blank'
        elif isinstance(t, int): acc = f'cons {B[t]} ({acc})'
        elif isinstance(t, Rep):
            if t.n.is_zero(): continue
            acc = f'rep ({lin_lean(t.n)}) {word_lean(t.word)} ({acc})'
    return acc

def rebracket(nf, pair, k):
    """nf: a token list in stream order (first = nearest to the head), whose front holds k copies of `pair`
    (pair = (0,1) for all three lemmas) possibly bracketed differently.  Returns (rewrites, rest) where rewrites is a
    list of Lean rewrite terms (applied in order to the natural term) after which the stream reads
    rep k pair REST, and rest is the token list of REST."""
    rewrites = []; i = 0; consumed = Lin(0); lits = 0
    # leading literal pairs: definitional (rep (n+1) = app pair (rep n ...))
    while i + 1 < len(nf) and isinstance(nf[i], int) and isinstance(nf[i + 1], int) and (nf[i], nf[i + 1]) == pair:
        i += 2; consumed = consumed + 1; lits += 1
    if i < len(nf) and isinstance(nf[i], Rep):
        r = nf[i]
        if r.word == pair:
            i += 1; consumed = consumed + r.n
            rest_after = nf[i:]
        elif i >= 1 and False:
            pass
        else:
            raise ValueError('unexpected repeat word %r' % (r,))
    elif i < len(nf) and isinstance(nf[i], int) and nf[i] == pair[0] and i + 1 < len(nf) and isinstance(nf[i + 1], Rep) and nf[i + 1].word == (pair[1], pair[0]):
        # x (y x)^n -> (x y)^n x
        r = nf[i + 1]; s_rest = nf[i + 2:]
        rewrites.append(f"rep_shift' {B[pair[0]]} {B[pair[1]]} ({lin_lean(r.n)}) ({to_lean_stream(s_rest)})")
        consumed = consumed + r.n
        nf = nf[:i] + [Rep(pair, r.n), pair[0]] + s_rest
        i += 1
        rest_after = nf[i:]
    else:
        rest_after = nf[i:]
        assert consumed == k, (consumed, k, nf)
        return rewrites, rest_after
    # absorb trailing literal pairs into the repeat
    while len(rest_after) >= 2 and isinstance(rest_after[0], int) and isinstance(rest_after[1], int) and (rest_after[0], rest_after[1]) == pair and consumed != k:
        n_now = nf[i - 1].n
        rewrites.append(f"rep_cons2 ({lin_lean(n_now)}) {B[pair[0]]} {B[pair[1]]} ({to_lean_stream(rest_after[2:])})")
        rest_after = rest_after[2:]; consumed = consumed + 1
        nf = nf[:i - 1] + [Rep(pair, n_now + 1)] + rest_after
    assert consumed == k, ('consumed %r, lemma count %r' % (consumed, k))
    return rewrites, rest_after

def lemma_segment(name, k, c_before):
    """Return (rewrites on the natural 'before' term, Lean proof term, lean 'after' config is implied by the lemma)."""
    if name in ('PASS', 'SHIFT'):
        nf = list(c_before.right)
        rewrites, rest = rebracket(nf, (0, 1), k)
        Lterm = left_term(c_before.left); Rterm = to_lean_stream(rest)
        return rewrites, f'{name.lower()} ({lin_lean(k)}) ({Lterm}) ({Rterm})', '2 * (%s)' % lin_lean(k)
    if name == 'CARRY':
        nf = nearest_first(c_before.left)
        rewrites, rest = rebracket(nf, (0, 1), k)
        Lterm = to_lean_stream(rest)
        r = list(c_before.right)
        assert isinstance(r[0], int) and r[0] == 1 and isinstance(r[1], int) and r[1] == 1, r
        Rterm = right_term(r[2:])
        return rewrites, f'carry ({lin_lean(k)}) ({Lterm}) ({Rterm})', '4 * (%s)' % lin_lean(k)
    raise ValueError(name)

def lean_name(n):
    return n.lower().replace('->', '_to_').replace('-', '_')

def emit(th):
    s = th["start"]; c = cfg(s[0], s[1], s[2], **s[3])
    start_term = cfg_term(c)
    vars_ = set(th['steps'].c)
    for t in c.left + c.right:
        if isinstance(t, Rep): vars_ |= set(t.n.c)
    binders = ' '.join(f'({v} : Nat)' for v in sorted(vars_))
    ctxs = []
    for t in c.left + c.right:
        if isinstance(t, Ctx) and t.name not in ctxs: ctxs.append(t.name)
    cbind = ' '.join(f'({x} : Tape)' for x in ctxs)
    stop = (lambda c: False) if th["halt"] else STOPS[th["stop"]]
    segs = []   # ('rfl', nsteps, before_term, after_term) or ('lemma', name, k, before_config)
    pending = 0; seg_start = cfg_term(c); halted = None
    try:
        for _ in range(10000):
            if stop(c): break
            before = c.copy()
            if try_lemma(c):
                if pending: segs.append(('rfl', pending, seg_start, cfg_term(before))); pending = 0
                nm, k = c.lemmas[-1]
                segs.append(('lemma', nm, k, before))
                seg_start = cfg_term(c)
            else:
                sstep(c); pending += 1
    except Halted as e:
        halted = str(e)
    if pending: segs.append(('rfl', pending, seg_start, cfg_term(c)))
    end_term = cfg_term(c)
    name = lean_name(th['name'])
    out = []
    out.append(f"/-- {th['name']}: {th['meaning']} -/")
    header = ' '.join(x for x in [f"theorem {name}", binders, cbind, ':'] if x)
    if halted:
        out.append(header)
        out.append(f"    steps {th['steps'].k} {start_term} = some {end_term} ∧ step {end_term} = none :=")
        out.append("  ⟨rfl, rfl⟩")
        return '\n'.join(out)
    e = th["end"]; want = cfg(e[0], e[1], e[2], **e[3]); want_term = cfg_term(want)
    out.append(header)
    out.append(f"    steps ({lin_lean(th['steps'])}) {start_term} = some {want_term} := by")
    bridge = want_term != end_term
    if bridge:
        out.append(f"  -- the run ends in the form {end_term}; the stated form is the same tape re-bracketed")
    counts = []; hyps = []
    for idx, seg in enumerate(segs):
        if seg[0] == 'rfl':
            _, n, before, after = seg
            out.append(f"  have h{idx} : steps {n} {before} = some {after} := rfl")
            counts.append(str(n)); hyps.append(f'h{idx}')
        else:
            _, nm, k, cb = seg
            rewrites, proof, count = lemma_segment(nm, k, cb)
            if rewrites and idx > 0:
                out.append(f"  conv at h{idx - 1} => rhs; rw [{', '.join(rewrites)}]")
            elif rewrites:
                out.append(f"  conv => lhs; rw [{', '.join(rewrites)}]")
            out.append(f"  have h{idx} := {proof}")
            counts.append(count); hyps.append(f'h{idx}')
    total = lin_lean(th['steps'])
    nested = counts[-1]
    for cnt in reversed(counts[:-1]): nested = f'{cnt} + ({nested})'
    out.append(f"  have e : {total} = {nested} := by omega")
    out.append(f"  rw [e]")
    chain = hyps[-1]
    for h in reversed(hyps[:-1]): chain = f'steps_seq {h} ({chain})'
    if bridge:
        out.append(f"  have hc := {chain}")
        out.append(f"  simpa only [rep_cons2, rep_shift'] using hc")
    else:
        out.append(f"  exact {chain}")
    return '\n'.join(out)

print("import BB6.Cycles\n")
print("/-! # The mark rules, each proved from the transition table along the Python prover's trace (generated by gen_rules.py). -/\n")
print("namespace BB6\n")
for th in THEOREMS:
    try:
        print(emit(th)); print()
    except Exception as ex:
        print(f"-- {th['name']}: generator failed: {type(ex).__name__}: {ex}\n")
print("end BB6")
