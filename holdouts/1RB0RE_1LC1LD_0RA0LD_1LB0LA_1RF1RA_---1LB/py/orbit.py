"""The orbit of (0, 5) under `next` (lean/Macro.lean): the fuel of each round, and the chance that a round halts.

usage: python3 orbit.py
"""


def next_(k, z):
    j = k // 2
    if k % 2 == 0:
        return (0, 3 * j + 2) if z == 0 else (3 * j + 1, z - 1)
    if z == 0:
        return None
    return (0, 3 * j + 5) if z == 1 else (3 * j + 4, z - 2)


def main():
    p, i, fuels = (0, 5), 0, [5]
    while len(fuels) < 4:
        p = next_(*p)
        i += 1
        if p is None:
            print("halts after", i, "rounds of next")
            return
        if p[0] == 0:
            fuels.append(p[1])
    print("fuel of rounds 1-4:", fuels, "after", i, "applications of next")
    # one round from k = 0 with fuel z halts iff z = the fuel spent before an odd u in u -> 3*ceil(u/2), u0 = 2
    N, u, spent, odd_at = 20000, 2, 0, set()
    while spent <= N:
        if u % 2:
            odd_at.add(spent)
        spent += 2 if u % 2 else 1
        u = 3 * ((u + 1) // 2)
    frac = sum(1 for z in range(1, N + 1) if z in odd_at) / N
    print(f"rounds with fuel 1..{N} that halt: {frac:.4f}")
    # check against rounds run with next_
    for z in range(1, 300):
        q = (0, z)
        while q is not None and not (q[0] == 0 and q != (0, z)):
            q = next_(*q)
        assert (q is None) == (z in odd_at), z
    print("the fixed-sequence criterion agrees with next for fuel 1..299")


if __name__ == "__main__":
    main()
