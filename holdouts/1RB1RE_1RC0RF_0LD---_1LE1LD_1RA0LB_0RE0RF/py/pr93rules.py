"""Write lean/PR93Rules.lean: the macro rules of DeepMind's busycoq PR 93 engine, proved for this machine.

usage (from the repo root):  python3 holdouts/1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF/py/pr93rules.py

This machine, mirrored and with its states renamed (A->C, B->D, C->E, D->A, E->B, F->F), is
M' = 1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF started in C.  PR 93 proves that T3 = 1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---
started in C halts (module M598).  M' is T3 with (1) T3's states E and F merged into F and T3's halt F1 replaced by 0LF,
and (2) the step D0 = 1RA replaced by the detour D0 = 1LE, E0 = 0RA, after which A reads the 1 just written and moves on
with 1RA: three steps that end where T3's one step ends, or a halt (E1) when the cell left of D holds a 1.
So every T3 rule whose trace never has D reading 0 next to a 1 is a rule of this machine, with two more steps per D0.

Each rule below is stated in this machine's own orientation, generated from PR 93's statement (busycoq notation, mirrored
frame) and proved along the symbolic run of tools/py/bbtools/symtm.py.  The three configurations of the engine are
CfgR l r = l A> 0100 r, CfgL l r = l <B 1 r, CfgJ l r = l <C 100 r in PR 93's frame; here (mirror, states renamed)
they are  r' 0010 <D l',  r' 1 E> l'... i.e. the head reads the first cell of l' in state E (CfgL) or A (CfgJ), and
the 0 of 0010 in state D (CfgR), where l' is PR 93's left side read outward and r' its right side mirrored.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
LEAN = os.path.join(HERE, "..", "lean")
sys.path.insert(0, os.path.join(HERE, "..", "..", "..", "tools", "py"))
from bbtools import symtm  # noqa: E402

MACHINE = "1RB1RE_1RC0RF_0LD---_1LE1LD_1RA0LB_0RE0RF"
NS = "H50436"
# PR 93 frame state -> this machine's state
ST = {"A": "D", "B": "E", "C": "A", "D": "B", "E": "C", "F": "F"}

# tokens: ('c', bits) | ('r', bits, expr)
def c(*b): return [("c", tuple(b))]
def rep(w, e): return [("r", tuple(w), e)]
def D(e): return c(1) + rep((1, 1), e) + c(0, 0)
def S(e): return c(1) + rep((0, 1), f"{e}+1")
def PL(e): return rep((1, 0), f"{e}+4") + rep((1, 1), e) + S("0") + S("0")
def DEF(a, k): return rep((1, 0), a) + rep((1,), k) + c(0, 1) + S("0")

def tok_str(t):
    if t[0] == "c": return " ".join(str(x) for x in t[1])
    return "(" + "".join(str(x) for x in t[1]) + ")^" + t[2].replace(" ", "")
def rev_tok(t):
    return ("c", tuple(reversed(t[1]))) if t[0] == "c" else ("r", tuple(reversed(t[1])), t[2])

def L(*words, base="L"):
    """busycoq  l <* w1 <* ... <* wk  (base l, or '0inf'): tokens outward from the head"""
    out = []
    for w in reversed(words): out += w
    return out, base
def Rr(*words, base="R"):
    out = []
    for w in words: out += w
    return out, base

def cfg(mode, left, right):
    """mode R/L/J of PR 93 with its left (outward) and right sides -> a symtm configuration string of this machine"""
    lo, lb = left; ro, rb = right
    if mode == "R": st, after, head = "A", c(1, 0, 0) + ro, c(0) + lo
    elif mode == "L": st, after, head = "B", c(1) + ro, lo
    else: st, after, head = "C", c(1, 0, 0) + ro, lo
    # this machine: left of the head = reverse of PR 93's cells right of the head; head and right = PR 93's left outward
    left_toks = [rev_tok(t) for t in reversed(after)]
    lb_s = "0^inf" if rb == "0inf" else ("Y" if rb == "R" else rb)
    rb_s = "0^inf" if lb == "0inf" else ("X" if lb == "L" else lb)
    s = " ".join([lb_s] + [tok_str(t) for t in left_toks if not (t[0] == "c" and not t[1])])
    s += f" {ST[st]}> " + " ".join([tok_str(t) for t in head if not (t[0] == "c" and not t[1])] + [rb_s])
    return s

Z = "0inf"
RULES = [
 ("rule_right", "R", L(), Rr(D("n")), "R", L(S("n")), Rr()),
 ("rule_left", "L", L(S("n")), Rr(), "L", L(), Rr(D("n"))),
 ("rule_blank", "R", L(), Rr(c(0, 0, 0)), "L", L(), Rr(D("0"), D("0"))),
 ("rule_even", "R", L(), Rr(rep((1, 1), "n+1"), c(0, 0)), "L", L(), Rr(D("n+1"), c(1, 0))),
 ("rule_restart", "L", L(c(1, 1, 1), rep((1, 0), "b+1")), Rr(), "R", L(rep((1, 0), "b+1")), Rr()),
 ("rule_overflow2", "L", L(c(1, 1), rep((1, 0), "b+1"), base=Z), Rr(), "R", L(rep((1, 1), "b+1"), rep((1, 0), "2"), base=Z), Rr(c(1))),
 ("rule_overflow1", "L", L(c(1), rep((1, 0), "b+1"), base=Z), Rr(D("n")), "R", L(rep((1, 1), "b"), rep((1, 0), "n+2"), base=Z), Rr(c(1, 0))),
 ("rule_collision", "L", L(c(0, 0, 1, 1, 0, 1)), Rr(), "J", L(), Rr(c(1, 1, 1, 1))),
 ("rule_leftJ", "J", L(S("n")), Rr(), "L", L(), Rr(D("n+1"))),
 ("rule_turnB", "L", L(c(1, 1)), Rr(D("n")), "R", L(rep((1, 0), "n+1")), Rr()),
 ("rule_turnJ", "J", L(c(1, 1, 1), rep((1, 0), "b")), Rr(), "R", L(rep((1, 0), "b+1")), Rr()),
 ("rule_finishP", "L", L(S("0"), c(0, 1), rep((1, 0), "b+1")), Rr(), "J", L(), Rr(D("b+1"))),
 ("rule_defect0", "R", L(), Rr(c(1, 0), D("0"), c(1), rep((1, 1), "m"), c(0)), "J", L(), Rr(c(1, 1, 1, 1), D("m"), c(1))),
 ("rule_defect1", "R", L(), Rr(c(1, 0), D("1"), c(1), rep((1, 1), "m"), c(0)), "L", L(), Rr(D("0"), D("0"), D("m+1"), c(1))),
 ("rule_defect2", "R", L(), Rr(c(1, 0), D("n+2"), c(1), rep((1, 1), "m"), c(0)), "R", L(S("0"), S("0"), rep((1, 1), "n"), rep((1, 0), "m+2")), Rr(c(1))),
 ("rule_defect_blank0", "R", L(), Rr(c(1, 0), D("0"), c(0, 0)), "R", L(S("0"), c(1, 0, 0, 1)), Rr()),
 ("rule_defect_blankS", "R", L(), Rr(c(1, 0), D("n+1"), c(0, 0)), "R", L(S("0"), S("0"), c(1), rep((1, 1), "n"), c(1, 0)), Rr()),
 # k = 0 is rule_right (S0 (10)^n read outward is S n); (10)^(2k) is written (1010)^k
 ("rule_paired", "R", L(), Rr(rep((1, 0, 1, 0), "k+1"), D("n")), "R", L(S("0"), rep((1, 1, 0, 1), "k+1"), rep((1, 0), "n")), Rr()),
 ("rule_emptyR", "R", L(), Rr(base=Z), "L", L(), Rr(D("0"), D("0"), base=Z)),
 ("rule_collide", "R", L(), Rr(c(1, 0), D("0"), D("0")), "J", L(), Rr(D("2"), c(1, 0))),
 ("rule_pairR", "R", L(), Rr(c(1, 0), D("n+2"), D("n+2")), "R", L(PL("n")), Rr(c(1, 0))),
 ("rule_zeroL_DD", "L", L(base=Z), Rr(D("a"), D("b")), "R", L(rep((1, 1), "a"), rep((1, 0), "b+2"), base=Z), Rr(c(1, 0))),
 ("rule_zeroL_D10_0", "L", L(base=Z), Rr(D("0"), c(1, 0)), "R", L(S("0"), base=Z), Rr(c(1))),
 ("rule_zeroL_D10_S", "L", L(base=Z), Rr(D("a+1"), c(1, 0)), "R", L(rep((1, 1), "a+1"), rep((1, 0), "2"), base=Z), Rr(c(1))),
 ("rule_zeroL_1", "L", L(c(1), base=Z), Rr(), "J", L(base=Z), Rr()),
 ("rule_zeroL_J_mid", "J", L(base=Z), Rr(D("n")), "L", L(base=Z), Rr(D("n+1"), c(1, 0))),
 ("def_k0_ML", "L", L(DEF("a+1", "0")), Rr(), "J", L(), Rr(D("a+1"))),
 ("def_k1_ML", "L", L(DEF("a", "1")), Rr(), "L", L(), Rr(D("0"), D("a"))),
 ("def_k2_ML", "L", L(DEF("a+1", "2")), Rr(), "L", L(), Rr(D("0"), D("0"), D("a"))),
 ("def_k1_MJ", "J", L(DEF("a", "1")), Rr(), "L", L(), Rr(D("0"), D("a+1"))),
 ("def_k2_MJ", "J", L(DEF("a+1", "2")), Rr(), "L", L(), Rr(D("0"), D("0"), D("a+1"))),
 ("def_02_ML", "L", L(DEF("0", "2")), Rr(D("d")), "R", L(DEF("d+1", "0")), Rr()),
 ("def_restart", "L", L(DEF("a+1", "k+3")), Rr(), "R", L(DEF("a+1", "k")), Rr()),
 ("def_turnJ", "J", L(DEF("a", "k+3")), Rr(), "R", L(DEF("a+1", "k")), Rr()),
 ("rule_mr_a0_DEF", "R", L(DEF("a", "k+3")), Rr(c(1, 0), D("0"), D("m")), "R", L(DEF("a+1", "k"), S("m+2")), Rr(c(1, 0))),
 ("rule_mr_a0_S_DEF", "R", L(DEF("a+1", "k+3"), S("s")), Rr(c(1, 0), D("0"), D("m")), "R", L(DEF("a+1", "k"), S("s+1"), S("m+2")), Rr(c(1, 0))),
]

def subst_side(side, v, val):
    toks, base = side
    out = []
    for t in toks:
        if t[0] == "r":
            e = symtm.parse_lin(t[2]); env = {u: symtm.Lin(u) for u in e.vars()}
            if v in env: env[v] = val
            out.append(("r", t[1], repr(symtm.lin(e.subs(env)))))
        else: out.append(t)
    return out, base

def prove_split(name, m0, l0, r0, m1, l1, r1, thms, fails, depth=0):
    """prove a rule; when a count may be 0 (NeedSplit), prove the cases count = 0 and count = v + 1 instead"""
    a, b = cfg(m0, l0, r0), cfg(m1, l1, r1)
    try:
        txt, fin = symtm.prove(MACHINE, name, a, b, doc=f"PR 93's `{name.split('_c')[0]}`: `{a}` reaches `{b}`.", rotate=True, max_seg=50, count_first=True)
        thms.append(txt); return
    except symtm.ProofError as e:
        msg = str(e)
        if "NeedSplit" in msg and depth < 3:
            ex = msg.split(")^")[-1].strip()
            v = sorted(symtm.parse_lin(ex).vars())[0]
            for tag, val in (("0", symtm.Lin(0)), ("s", symtm.Lin(v) + 1)):
                prove_split(f"{name}_c{v}{tag}", m0, subst_side(l0, v, val), subst_side(r0, v, val), m1,
                            subst_side(l1, v, val), subst_side(r1, v, val), thms, fails, depth + 1)
            return
        fails.append((name, msg[:300])); print("FAIL", name, a, "->", b, msg[:300])

def main():
    thms, fails = [], []
    for rule in RULES:
        prove_split(*rule, thms, fails)
    doc = ("The macro rules of DeepMind's busycoq PR 93 engine (module M598), proved for " + MACHINE +
           " in its own orientation; generated by `py/pr93rules.py`, do not edit by hand.  Each rule's start and end are"
           " the mirror image of PR 93's statement with the states renamed (PR 93's A, B, C are D, E, A here).  Every rule"
           " holds for every count and every tape around: in none of these runs does B read 0 next to a 1, the only way"
           " this machine's steps differ from PR 93's machine (where they differ, this machine takes two more steps).")
    open(os.path.join(LEAN, "PR93Rules.lean"), "w").write(symtm.rules_file("Machine", NS, thms, doc))
    print(len(thms), "rules written,", len(fails), "failed")

if __name__ == "__main__":
    main()
