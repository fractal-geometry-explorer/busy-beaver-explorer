"""Lean proofs that two right-tape token lists denote the same tape: both are brought to symtm's canonical form
by the moves of `symtm.canon`, each move proved by a lemma of TM.Basic (rep_rotate, rep_add, cons_false_blank).

`rule` turns a symbolic run between two tape forms into a Lean theorem stated with the forms' definitions (`defn`):
the run (`symtm.prove`), then the equalities that rebracket its end tapes into the stated form."""
import os
import re
import sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools', 'py'))
from bbtools.symtm import Rep, Blank, Lin, right_term, _word, prove, Config, cfg_term  # noqa: E402

M = "1RB0LE_1RC---_1RD1RE_1LA0RF_0RC0LA_0LC0RB"


def canon_moves(seq):
    """Mirror of symtm.canon on a right token list; returns (final, [(i, before_list, after_list, proof)]) where the
    move rewrites the suffix starting at index i and proof proves right_term(before[i:]) = right_term(after[i:])."""
    moves = []
    out = list(seq)

    def rec(i, new_out, pf):
        moves.append((i, list(out), list(new_out), pf))

    # expand constant parts of counts
    i = 0
    while i < len(out):
        t = out[i]
        if isinstance(t, Rep) and not t.n.is_zero():
            const, var = t.n.k, Lin(0, t.n.c)
            if const and not var.is_zero():
                s = right_term(out[i + 1:])
                new = out[:i] + [Rep(t.word, var)] + list(t.word) * const + out[i + 1:]
                rec(i, new, f"rep_add ({var.lean()}) {const} {_word(t.word)} ({s})")
                out = new
            elif var.is_zero():
                new = out[:i] + list(t.word) * const + out[i + 1:]
                rec(i, new, "rfl")
                out = new
                continue
        i += 1
    changed = True
    while changed:
        changed = False
        for i in range(len(out)):
            t = out[i]
            if not isinstance(t, Rep) or t.n.is_zero():
                continue
            L = len(t.word)
            pre = out[max(0, i - L):i]
            if len(pre) == L and all(isinstance(x, int) for x in pre) and tuple(pre) == t.word:
                s = right_term(out[i + 1:])
                new = out[:i - L] + [t] + list(t.word) + out[i + 1:]
                rec(i - L, new, f"rep_rotate ({t.n.lean()}) {_word(t.word)} {_word(t.word)} {_word(t.word)} rfl ({s})")
                out = new; changed = True
                break
            if L > 1 and i >= 1 and isinstance(out[i - 1], int) and out[i - 1] == t.word[-1]:
                x = out[i - 1]
                w2 = (x,) + t.word[:-1]
                s = right_term(out[i + 1:])
                new = out[:i - 1] + [Rep(w2, t.n), x] + out[i + 1:]
                rec(i - 1, new, f"rep_rotate ({t.n.lean()}) {_word((x,))} {_word(t.word)} {_word(w2)} rfl ({s})")
                out = new; changed = True
                break
            if i >= 1 and isinstance(out[i - 1], Rep) and out[i - 1].word == t.word and not out[i - 1].n.is_zero():
                m, n = out[i - 1].n, t.n
                s = right_term(out[i + 1:])
                new = out[:i - 1] + [Rep(t.word, m + n)] + out[i + 1:]
                rec(i - 1, new, f"by rw [← rep_add] <;> congr 1 <;> omega")
                out = new; changed = True
                break
    while len(out) >= 2 and out[-1] == Blank() and out[-2] == 0:
        new = out[:-2] + [Blank()]
        rec(len(out) - 2, new, "cons_false_blank")
        out = new
    return out, moves


def _chain(prefix, moves):
    lines, names = [], []
    for k, (i, a, b, pf) in enumerate(moves):
        nm = f"{prefix}{k}"
        sa, sb = right_term(a[i:]), right_term(b[i:])
        lines.append(f"  have {nm} : {right_term(a)} = {right_term(b)} := by")
        lines.append(f"    rw [show {sa} = {sb} from {pf}]")
        names.append(nm)
    return lines, names


def mirror(left_tokens):
    """A left token list as the right token list with the same Lean term (`left_term(t) = right_term(mirror(t))`)."""
    return [Rep(tuple(reversed(t.word)), t.n) if isinstance(t, Rep) else t for t in reversed(left_tokens)]


def used(names, text):
    """The names that occur in text as words."""
    return [v for v in names if re.search(r"\b%s\b" % re.escape(v), text)]


def tape_eq(name, t1, t2, vars_, doc=None, ctxs=()):
    """Lean theorem name : right_term(t1) = right_term(t2) (for left tapes pass `mirror(...)` of both)."""
    c1, m1 = canon_moves(t1)
    c2, m2 = canon_moves(t2)
    if c1 != c2:
        raise ValueError(f"{name}: different canonical forms\n{c1}\n{c2}")
    lines = [f"/-- {doc} -/"] if doc else []
    terms = right_term(t1) + " " + right_term(t2)
    vars_ = used(vars_, terms)
    ctxs = used(ctxs, terms)
    b = f" ({' '.join(vars_)} : Nat)" if vars_ else ""
    b += f" ({' '.join(ctxs)} : Tape)" if ctxs else ""
    lines.append(f"theorem {name}{b} :")
    lines.append(f"    {right_term(t1)} = {right_term(t2)} := by")
    l1, n1 = _chain("e", m1)
    l2, n2 = _chain("f", m2)
    lines += l1 + l2
    def trans(ns):
        if not ns:
            return "rfl"
        acc = ns[-1]
        for n in reversed(ns[:-1]):
            acc = f"{n}.trans ({acc})"
        return acc
    lines.append(f"  exact ({trans(n1)}).trans ({trans(n2)}).symm")
    return "\n".join(lines) + "\n"


def defn(name, args, fn, doc):
    c = Config.parse(fn(*args))
    return f"/-- {doc} -/\ndef {name} ({' '.join(args)} : Nat) : Config :=\n  {cfg_term(c)}\n"


def rule(name, start, end, vs, lhs, rhs, doc, machine=None):
    """Theorem `name`: steps N lhs = some rhs, where lhs/rhs are Lean terms for the forms `start`/`end`, for all
    values of the variables `vs` and all tapes in the contexts of `start` (L, R, ...)."""
    raw, fin = prove(machine or M, name + "_raw", start, end, rotate=True, count_first=True,
                     doc=f"The symbolic run of `{name}`, ending as the run writes it.")
    tgt = Config.parse(end)
    ctxs = []
    for x in Config.parse(start).contexts() + tgt.contexts():
        if x not in ctxs:
            ctxs.append(x)
    out, rws = [raw], []
    if fin.left != tgt.left:
        out.append(tape_eq(name + "_l", mirror(fin.left), mirror(tgt.left), sorted(vs),
                           doc=f"The left tape at the end of `{name}_raw`, rebracketed.", ctxs=ctxs))
        rws.append(f"{name}_l {' '.join(used(sorted(vs) + ctxs, right_term(mirror(fin.left)) + ' ' + right_term(mirror(tgt.left))))}")
    if fin.right != tgt.right:
        out.append(tape_eq(name + "_r", fin.right, tgt.right, sorted(vs),
                           doc=f"The right tape at the end of `{name}_raw`, rebracketed.", ctxs=ctxs))
        rws.append(f"{name}_r {' '.join(used(sorted(vs) + ctxs, right_term(fin.right) + ' ' + right_term(tgt.right)))}")
    binders = (f" ({' '.join(vs)} : Nat)" if vs else "") + (f" ({' '.join(ctxs)} : Tape)" if ctxs else "")
    # rewrite only the end configuration (the start may contain the same subterm)
    rw = (f"  have e : (some {cfg_term(fin)} : Option Config) = some {cfg_term(tgt)} := by\n"
          f"    rw [{', '.join(rws)}]\n  rw [e] at h\n") if rws else ""
    out.append(f"""/-- {doc} -/
theorem {name}{binders} :
    steps ({fin.steps.lean()}) ({lhs}) = some ({rhs}) := by
  have h := {name}_raw {' '.join(sorted(vs) + ctxs)}
{rw}  exact h
""")
    return out
