"""Write lean/MapRun.lean: the run from blank tape rebuild after rebuild by the checked rebuild map of lean/Map.lean.

For each rebuild state (k, m, r) — a single block of 3(k + 1) cells, the counter in round m with r sub-rounds left —
this computes the hint `rstep` needs (the 0 bit p where the counter is cut, the number c of digits the transient may
touch, the stretches of the transient, the next round m') with Python mirrors of the Lean functions (`subsF`,
`gfastF`, `rstep`, move for move), checks that the next state is the one of py/rebuild_map.py, and writes the hints with the states.
The kernel evaluates `rstep` once per rebuild (`decide +kernel`); `reach_step` (from `rstep_sound`) chains them into a
run of the machine.  The hint takes the smallest margins (bits of the counter, digits of the list) for which the
transient stays inside the prefixes; with no 0 bit of the counter above them the counter is not cut (p = m).

usage: python3 py/gen_map.py R > lean/MapRun.lean        (rebuilds 4 .. R)
"""
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import passm, rebuild_map as rm  # noqa: E402
import gen_chain as gc  # noqa: E402
sys.set_int_max_str_digits(0)
FUEL = 1000000


# ---------------------------------------------------------------- mirrors of lean/Frame.lean and lean/Map.lean
def two(x):
    return len(x) >= 2


def safe(s):
    lb, ph, k, us = s
    return two(lb) and (k != 0 or two(us))


def run_pass_f(s, top=False):
    """runPassF: ("moment", bs, l, us, n) | ("halt",) | None (would read past the prefix)"""
    n = 0
    for _ in range(FUEL):
        if not (two(s[0]) if top else safe(s)): return None
        r = passm.pstep(s)
        if r[0] == "next": s = r[1]; n += r[2]
        elif r[0] == "done": return ("moment", r[1], r[2], r[3], n + r[4])
        else: return ("halt",)
    return None


def sub_f(bs, l, us, top=False):
    if not two(bs): return None
    if bs[0] < 1 or l < 1: return ("stuck",)
    p, rest = bs[0], bs[1:]
    s = ([rest[0] + 3] + rest[1:], "A", p, [l - 1] + list(us)); n0 = (l - 1) + 3 * (p - 1) + 15
    r = run_pass_f(s, top)
    if r is None or r[0] != "moment": return r
    return ("moment", r[1], r[2], r[3], r[4] + n0)


def gpop_f(us, n):
    i = 0
    while True:
        if i == len(us): return None
        u = us[i]
        if u == 3: i += 1; n += 1; continue
        if u >= 4: return ("some", (4 * n + 5, [u - 4] + us[i + 1:]))
        if u == 0:
            if i + 1 == len(us): return None
            if us[i + 1] >= 2: return ("some", (4 * n + 4, [us[i + 1] - 2] + us[i + 2:]))
        return ("none",)


def gstep_f(x):
    l, us = x
    if l >= 2: return ("some", (1, [l - 2] + us))
    if l == 1: return gpop_f(us, 0)
    return ("none",)


def gfast_f(N, x):
    for _ in range(FUEL):
        if N == 0: return x
        s = gc.pick(N, (x[0] - 1) // 4)
        y = gstep_f((x[0] - 4 * s, x[1]))
        if y is None or y[0] != "some": return None
        y = y[1]; N -= 2 ** s; x = (y[0] + 4 * s, y[1])
    return None


def gmax_f(N, x):
    """the most sub-rounds (<= N) the counter makes on the prefix, by the same jumps as gen_chain.gmax"""
    M = 0
    while N > 0:
        s = gc.pick(N, (x[0] - 1) // 4)
        while True:
            y = gstep_f((x[0] - 4 * s, x[1]))
            if (y is not None and y[0] == "some") or s == 0: break
            s -= 1
        if y is None or y[0] != "some": break
        y = y[1]; N -= 2 ** s; M += 2 ** s; x = (y[0] + 4 * s, y[1])
    return M


def sig(F):
    return sum(d + 1 for d in F)


def czb(bs):
    t = 0
    while t < len(bs) and not bs[t]: t += 1
    if t == len(bs): return (4 * t + 1, [])
    return (4 * t + 1, zone_of(bs[t + 1:]))


def zone_of(bs):
    z = [3]
    for b in bs:
        if b: z[-1] += 4
        else: z.append(3)
    return z


def bits(p, r):
    return [bool((r >> i) & 1) for i in range(p)]


def decode(x):
    l, Z = x
    out = [False] * ((l - 1) // 4) + [True]
    for i, g in enumerate(Z):
        out += [True] * ((g + 1) // 4 - 1)
        if i + 1 < len(Z): out.append(False)
    return out


def valB(L):
    return sum(1 << i for i, b in enumerate(L) if b)


def reg(l, Z):
    return l % 4 == 1 and all(u % 4 == 3 for u in Z)


def hint(k, m, r):
    """(hint, next state) for the rebuild state (k, m, r): the smallest margins that work"""
    for a in (8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 10 ** 9):
        try: return hint1(k, m, r, a)
        except AssertionError:
            if a == 10 ** 9: raise


def hint1(k, m, r, a):
    J = rm.local_word(r)[0]
    c = min(k, 4 * J + 5 * a)
    p, z = min(3 * J + a, m), a // 2     # the (a/2)-th 0 bit from 3J + a on, so that the zone prefix has gaps to spare
    while p < m:
        if not (r >> p) & 1:
            z -= 1
            if z == 0: break
        p += 1
    assert c <= k and r % 2 ** p != 0, (p, m, c, k)
    l0, Z0 = czb(bits(p, r))
    if l0 >= 5: x = (5, [l0 - 5] + Z0)
    else:
        assert l0 == 1 and Z0[0] >= 2; x = (4, [Z0[0] - 2] + Z0[1:])
    top = p == m
    # top: no cut, nothing right of the zone: the counter exact (`gfast`), the pass machine may read the zone's end
    F = [0] * c; segs = []
    while True:
        if reg(*x) and segs: break
        if top:
            M = gc.gmax(gc.T(F), x)[0]
        else:
            M = gmax_f(gc.T(F), x)
        if M > 0:
            y = gc.gfast(M, x)[0] if top else gfast_f(M, x)
            assert y is not None
            F2 = gc.Tinv(gc.T(F) - M); assert sig(F2) == sig(F), "the list prefix is too short"
            segs.append(("adv", M)); F, x = F2, y
            continue
        bs, l, Z = [3 * d + 2 for d in F], x[0], list(x[1]); N = 0
        while True:
            o = sub_f(bs, l, Z, top)
            assert o is not None and o[0] == "moment", ("pass", o)
            _, bs, l, Z, _ = o; N += 1
            g = gc.gstep((l, Z)) if top else gstep_f((l, Z))
            ok = g is not None and (top or g[0] == "some")
            if all(b % 3 == 2 for b in bs) and ok: break
        segs.append(("pass", N)); F, x = [(b - 2) // 3 for b in bs], (l, Z)
    L = decode(x)
    assert czb(L) == (x[0], x[1]) and any(L)
    if p == m: m1, r1 = len(L), valB(L)
    else:
        m1 = len(L) + 1 + (m - p - 1)
        r1 = valB(L) + 2 ** (len(L) + 1) * (r >> (p + 1))
    K = k - c
    N = gc.T(F) + 2 ** sig(F) * (2 ** K - 1)
    V = 2 ** (m1 + 1) - r1 + N
    m2 = V.bit_length() - 1
    nxt = (sig(F) + K, m2, 2 ** (m2 + 1) - V)
    return (p, c, segs, m2), nxt


def lean_hint(h):
    p, c, segs, m2 = h
    ss = ", ".join(f".{kind} {n}" for kind, n in segs)
    return f"⟨{p}, {c}, [{ss}], {m2}⟩"


def main():
    R = int(sys.argv[1]); t0 = time.time()
    k, m, r = rm.third()
    assert (k, m, r) == (29, 28, 28950), (k, m, r)
    states, hs = [(k, m, r)], []
    for i in range(4, R + 1):
        h, nxt = hint(k, m, r)
        want = rm.step(k, m, r)[:3]
        assert nxt == want, (i, nxt[0], want[0])
        hs.append(h); states.append(nxt); k, m, r = nxt
    sys.stderr.write(f"{len(hs)} hints, {sum(len(h[2]) for h in hs)} stretches; rebuild {R}: single block "
                     f"{3 * (k + 1)} cells, round {m} [{time.time() - t0:.0f} s]\n")
    out = [f"""import Map
import Transient

/-!
# 1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---: the run from blank tape to rebuild {R}, by the checked rebuild map

Generated by `py/gen_map.py {R}`; do not edit by hand.  `s i` is the rebuild state of rebuild `i` (`rcfg k m r` of
`Map.lean`: a single block of `3 (k + 1)` cells, the counter in round `m` with `r` sub-rounds left); `s 3` is the third
single block (`third_state`).  For each rebuild the kernel evaluates `rstep` once on its hint (`step_i`), and
`reach_step` (from `rstep_sound`) adds it to the run.  The transients are evaluated on prefixes of the list and the
counter, whatever the size of the single block (`Frame.lean`); everything else is arithmetic on the numbers
(`Bits.lean`).  The states are written out so that each check starts from numbers, not from the previous check.
-/

namespace H4320

open TM

-- the longest transients (rebuilds 140 and 142) recurse deeper than the default allows
set_option maxRecDepth 100000

/-- The third single block, a rebuild state. -/
theorem third_state : ∃ n, steps n init = some (rcfg 29 28 28950) := by
  obtain ⟨n₁, h₁⟩ := second_transient
  have e : ((9 : Nat), [3, 3, 3, 3, 3, 3, 3]) = cz 9 4 := by decide
  have hg := giter_cz 536840942 9 4 28 (by decide) (by decide) (by decide) (by decide)
  obtain ⟨n₂, h₂⟩ := collapse 536840942 1 D2 (cz 9 4) _ T_D2 hg
  rw [mass_D2, show 2 ^ (28 + 1) - (2 ^ (9 + 1) - 4 + 536840942) = 28950 by decide] at h₂
  rw [← e] at h₂
  exact ⟨n₁ + n₂, steps_seq trans h₁ h₂⟩

theorem reach_3 : ∃ n, steps n init = some (rcfg (29, 28, 28950).1 (29, 28, 28950).2.1 (29, 28, 28950).2.2) :=
  third_state
"""]
    prev = "(29, 28, 28950)"
    for i, (h, st) in enumerate(zip(hs, states[1:]), start=4):
        out.append(f"""
def s{i} : Nat × Nat × Nat := {st}

theorem step_{i} : rstep {FUEL} {lean_hint(h)} {prev}.1 {prev}.2.1 {prev}.2.2 = some s{i} := by decide +kernel

theorem reach_{i} : ∃ n, steps n init = some (rcfg s{i}.1 s{i}.2.1 s{i}.2.2) := reach_step reach_{i - 1} step_{i}
""")
        prev = f"s{i}"
    out.append(f"""
/-- **The single block of rebuild {R}**: {3 * (k + 1)} cells.  The run from blank tape reaches it, with a regular
counter, without a halt before it. -/
theorem single_map_{R} : ∃ m r n, steps n init = some (rcfg {k} m r) :=
  ⟨_, _, reach_{R}⟩

end H4320
""")
    print("".join(out))


if __name__ == "__main__":
    main()
