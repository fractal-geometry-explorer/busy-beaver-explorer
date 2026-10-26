"""Machine-checked proofs of the mark rules for 1RB0RE_1LC0RA_1LA1LD_1LA---_0RF0LB_0LD1RE.

Every theorem says: from the start configuration, the machine reaches the end configuration in the stated
number of steps, for every value of the variables (m, j, k >= 0) and for any tape L and R around the pattern
(L and R are never read). Proofs use single machine steps and the three cycle lemmas from symtm.

Notation: tapes are written left to right, 'S>' marks the head (in state S) on the cell to its right,
(10)^m is 10 repeated m times, 0^inf is blank tape.
"""
from symtm import *
from symtm import _unroll_front, _unroll_back

m, j, k = Lin("m"), Lin("j"), Lin("k")

def is_pass_position(c):
    """Head in state E on the last 0 of a run 000 (the canonical position after a gap step)."""
    if c.state != "E" or c.steps.is_zero(): return False
    try:
        r = list(c.right); x = _unroll_front(r)
        l = list(c.left); a = _unroll_back(l); l2 = l[:-1]; b = _unroll_back(l2); l3 = l2[:-1]; d = _unroll_back(l3)
    except (TouchContext, NeedSplit):
        return False
    return x == 0 and a == 0 and b == 0 and d == 1

def at_left_context(c):
    cl = canon(c.left)
    return len(cl) == 1 and isinstance(cl[0], (Ctx, Blank))

STOPS = {"pass": is_pass_position, "left": at_left_context}

def cfg(left, state, right, **v):
    def side(s):
        out = []
        for part in s.split(" | "):
            out += [Blank()] if part.strip() == "0^inf" else tokens(part, **v)
        return out
    return Config(side(left), state, side(right))

THEOREMS = []
def theorem(name, start, stop, end, steps, meaning, halt=None):
    THEOREMS.append(dict(name=name, start=start, stop=stop, end=end, steps=steps, meaning=meaning, halt=halt))

V = dict(m=m, j=j)
# ---- closing in on a marker
theorem("BOUNCE", ("L 0 0", "E", "0 (10)^m2 1 1 0 R", dict(m2=m + 2)), "pass",
        ("L 0 1 0 0", "E", "0 (10)^m 1 1 0 1 0 R", V), 6 * m + 30,
        "One bounce off a marker: the gap moves 2 right, the marker 2 left.")
theorem("SWAP", ("L 1 0 0", "E", "0 1 1 0 R", {}), "pass",
        ("L 1 1 0 0", "E", "0 1 0 R", {}), Lin(21),
        "No stripes left between gap and marker: the marker ends up just left of the gap, which moves 1 right.")
theorem("MERGE", ("L 1 0 0", "E", "0 1 0 1 1 0 R", {}), "left",
        ("L", "A", "1 1 1 0 1 0 0 1 0 R", {}), Lin(31),
        "Two stripe cells between: gap and marker become a wall 00, and a packet 111 heads left.")
# ---- closing in on a wall or blank tape
theorem("WALLBOUNCE", ("L 0 0", "E", "0 (10)^m1 0 R", dict(m1=m + 1)), "pass",
        ("L 0 1 0 0", "E", "0 (10)^m 0 R", V), 6 * m + 12,
        "One bounce off a wall (or the blank end): the gap moves 2 right, the wall stays.")
# ---- the gap meets a wall: E0 F0 D0, then a shift runs right over j stripe pairs to the next mark
theorem("MEET->marker", ("L 1 0 0", "E", "0 0 (10)^j 1 1 0 R", V), "pass",
        ("L (10)^j 1 0 1 0 1 0 0", "E", "0 R", V), 2 * j + 8,
        "Gap and wall vanish; the shift uses up the marker and a gap opens where the marker was.")
theorem("MEET->wall", ("L 1 0 0", "E", "0 0 (10)^j 0 1 R", V), "left",
        ("L", "A", "1 1 (10)^j 1 0 1 1 1 R", V), 6 * j + 13,
        "Gap and wall vanish; the next wall becomes a block 111, and a packet heads left.")
theorem("MEET->block", ("L 1 0 0", "E", "0 0 (10)^j 1 1 1 0 R", V), "left",
        ("L", "A", "1 1 (10)^j 1 0 1 0 1 0 0 R", V), 6 * j + 19,
        "Gap and wall vanish; the block becomes a wall two cells further right, and a packet heads left.")
theorem("MEET->blank", ("L 1 0 0", "E", "0 0 (10)^j | 0^inf", V), "left",
        ("L", "A", "1 1 (10)^j 1 0 1 1 | 0^inf", V), 6 * j + 13,
        "Gap and wall vanish; the shift reaches blank tape, which gains an end marker 11; a packet heads left.")
theorem("GAP->blankend", ("L 1 0 0", "E", "0 | 0^inf", {}), "left",
        ("L", "A", "1 1 1 0 1 1 | 0^inf", {}), Lin(13),
        "A gap with nothing to its right: the end gains a marker 3 cells further right, and a packet heads left.")
theorem("MEET->endmarker", ("L 1 0 0", "E", "0 0 (10)^j 1 1 | 0^inf", V), "left",
        ("L", "A", "1 1 (10)^j 1 0 1 0 1 0 1 1 | 0^inf", V), 6 * j + 29,
        "Gap and wall vanish; the shift uses up the end marker, the new gap meets the blank end, a new end marker forms 3 cells further right, and a packet heads left.")
# ---- a pass reaches a block 111 (after m stripe pairs): it becomes a wall, a shift runs j pairs to the next mark
theorem("BLOCK->marker", ("L 1 0 0", "E", "0 (10)^m 1 1 1 0 (10)^j 1 1 0 R", V), "pass",
        ("L 1 0 0 (01)^m 0 (01)^j 0 1 0 1 0 0", "E", "0 R", V), 2 * j + 2 * m + 9,
        "The block becomes a wall, the old gap stays (asleep), and a gap opens where the marker was.")
theorem("BLOCK->wall", ("L 1 0 0", "E", "0 (10)^m 1 1 1 0 (10)^j 0 1 R", V), "pass",
        ("L 1 0 0 (01)^m 1 0 0", "E", "0 (10)^j 1 1 1 R", V), 6 * j + 2 * m + 17,
        "The block becomes a wall; the next wall becomes a block; the packet comes back and the first wall turns into a marker and a gap.")
theorem("BLOCK->block", ("L 1 0 0", "E", "0 (10)^m 1 1 1 0 (10)^j 1 1 1 0 R", V), "pass",
        ("L 1 0 0 (01)^m 1 0 0", "E", "0 (10)^j 1 0 1 0 0 R", V), 6 * j + 2 * m + 23,
        "The block becomes a wall; the next block becomes a wall 2 cells right; the first wall turns into a marker and a gap.")
theorem("BLOCK->blank", ("L 1 0 0", "E", "0 (10)^m 1 1 1 0 (10)^j | 0^inf", V), "pass",
        ("L 1 0 0 (01)^m 1 0 0", "E", "0 (10)^j 1 1 | 0^inf", V), 6 * j + 2 * m + 17,
        "The block becomes a wall; the blank end gains a marker; the wall turns into a marker and a gap.")

# ---- a packet heading left reaches a mark. CARRY takes every 10 pair it can, so it also takes the 1 0 formed by the
#      last 1 of a marker or block and the 0 after it: the head then sits right after the mark's first 1 (or first two).
theorem("PACKET->gap", ("L 0 0 0", "A", "1 1 R", {}), "pass",
        ("L 0 1 0 0", "E", "0 R", {}), Lin(7),
        "Gap step: the gap moves 2 right.")
theorem("PACKET->wall", ("L 1 0 0", "A", "1 1 R", {}), "pass",
        ("L 1 1 0 0", "E", "0 R", {}), Lin(7),
        "The wall becomes a marker with a gap just right of it.")
theorem("PACKET->marker", ("L 1 0 1", "A", "1 1 R", {}), "left",
        ("L", "A", "1 1 1 1 0 R", {}), Lin(5),
        "Marker pass: the packet crosses the marker, which stays where it is.")
theorem("PACKET->leftend", ("0^inf", "A", "1 1 R", {}), "pass",
        ("0^inf | 1 0 0", "E", "0 R", {}), Lin(7),
        "A new gap starts at the left end; the tape grows 2 cells to the left.")
theorem("PACKET->leftend-marker", ("0^inf | 1", "A", "1 1 R", {}), "pass",
        ("0^inf | 1 0 0", "E", "0 1 0 0 R", {}), Lin(18),
        "A marker on the first cell turns into a wall, a new gap starts at the left end; the tape grows 4 cells.")
theorem("PACKET->marker-after-gap", ("L 1 0 0 0 1", "A", "1 1 R", {}), "left",
        ("L", "A", "1 1 1 0 1 0 0 R", {}), Lin(15),
        "A packet reaching a marker directly preceded by a gap: gap and marker become a wall and the packet goes on left.")
theorem("PACKET->block", ("L 0 1 1", "A", "1 1 R", {}), None, None, Lin(4),
        "The machine halts (D reads 1).", halt="D1")


def prove(th):
    s = th["start"]; c = cfg(s[0], s[1], s[2], **s[3])
    if th["halt"]:
        try:
            run(c, lambda c: False, max_iter=1000)
        except Halted as e:
            return str(e) == th["halt"] and c.steps == th["steps"], c
        return False, c
    run(c, STOPS[th["stop"]])
    e = th["end"]; want = cfg(e[0], e[1], e[2], **e[3])
    return same_config(c, want) and c.steps == th["steps"], c


def prove_iteration(name, step_th, shift_left, shift_right, var_step):
    """Induction on the number of repetitions: the end of one application must be the start pattern again,
    with the exponent lowered by var_step and with shift_left/shift_right added to the contexts."""
    s = step_th["start"]; e = step_th["end"]
    # instantiate the start pattern with exponent m (the one-step theorem lowers m+var_step to m)
    if name == "BOUNCE":
        nxt = cfg("L " + shift_left + " 0 0", "E", "0 (10)^m 1 1 0 " + shift_right + " R", m=m)
    else:
        nxt = cfg("L " + shift_left + " 0 0", "E", "0 (10)^m 0 " + shift_right + " R", m=m)
    endc = cfg(e[0], e[1], e[2], **e[3])
    return same_config(endc, nxt)


if __name__ == "__main__":
    print("cycle lemmas:")
    for name, ok, h in prove_cycles():
        print(f"  {name:6s} {'proved' if ok else 'FAILED'}   ({h})")
    print("theorems:")
    allok = True
    for th in THEOREMS:
        try:
            ok, c = prove(th)
        except Exception as ex:
            ok, c = False, None; print("   exception", type(ex).__name__, ex)
        allok &= ok
        print(f"  {th['name']:24s} {'proved' if ok else 'FAILED'}  steps {th['steps']}")
    by = {t["name"]: t for t in THEOREMS}
    print("induction steps (k repetitions):")
    for name in ("BOUNCE", "WALLBOUNCE"):
        ok = prove_iteration(name, by[name], "0 1", "1 0" if name == "BOUNCE" else "", 2 if name == "BOUNCE" else 1)
        # step total: sum over i < k of the one-step count with exponent m + (k-1-i)*var_step
        if name == "BOUNCE":
            total = lambda K, M: 6 * K * M + 6 * K * K + 24 * K
            ok &= all(sum(6 * (M + 2 * i) + 30 for i in range(K)) == total(K, M) for K in range(30) for M in range(30))
            stmt = "L 0 0 E>0 (10)^(m+2k) 1 1 0 R  ->  L (01)^k 0 0 E>0 (10)^m 1 1 0 (10)^k R   in 6km + 6k^2 + 24k steps"
        else:
            total = lambda K, M: 6 * K * M + 3 * K * K + 9 * K
            ok &= all(sum(6 * (M + i) + 12 for i in range(K)) == total(K, M) for K in range(30) for M in range(30))
            stmt = "L 0 0 E>0 (10)^(m+k) 0 R  ->  L (01)^k 0 0 E>0 (10)^m 0 R   in 6km + 3k^2 + 9k steps"
        allok &= ok
        print(f"  {name + '^k':12s} {'proved' if ok else 'FAILED'}   {stmt}")
    print("ALL PROVED" if allok else "SOME FAILED")
