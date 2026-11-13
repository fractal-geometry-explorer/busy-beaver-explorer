"""The counter model of 1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---.

A state (n0, G) is the configuration  C> 0 10 x^n0 [1 a^d x^n for (d, n) in G] 1 0^inf  (x = 1110, a = 10, blank
tape on the left), the head in C at the left end.  `bounce` is one round trip of the head (lean/Model.lean,
`bounceM`, proved to be the machine's run; `bounce_lean` here is a line-by-line transcription of it):

  * the borrow passes the leading groups (0, m+1): each becomes (2, m);
  * at a group (e+1, n) the digit drops to e and n0 gains one x; an empty group (0,0) left in front of a group
    (1, n') merges with it into the block before (1 . 1 10 = 1110);
  * past the last group (every digit 0) the round ends:
        (n0; (0,m1+1), ..., (0,mk+1))  ->  (0; (1,n0+1), (0,m1+1), ..., (0,m_(k-1)+1), (0,mk), (0,0))
  * t empty groups (0,0) at the end: t = 1 is removed, t = 2 stays (an endless supply: the "A" phase),
    t = 3 becomes (1,0) (the "F" event);
  * an empty group with a nonempty group of digit 0 after it, or 4 or more empty groups at the end: the machine
    halts;
  * one or two empty groups and then a group with digit e+2 (never seen in the run): the machine turns round there,
        (n0; Z, (0,0), (e+2,n), rest)  ->  (0; (1,n0+1), Z, (0,0), (e,n), rest)         (Z the passed groups)
    and a round with no group at all gives (n0; ) -> (0; (1,n0), (0,0)).
The model is defined on every state (lean: bounceM_ne_stuck).  `py/model.py random N` compares it with the machine
on N random states.

`jump` applies many bounces at once (exact; the passes of group i happen at the decrements of the counter value v
with 3^(i+1) | v).  usage:

    python3 py/model.py far SECONDS      # run the model from the configuration of step 403 for SECONDS seconds
    python3 py/model.py check FILE       # compare with the counter lines of c/cdump (every bounce)
    python3 py/model.py random N         # compare one bounce with the machine on N random states
"""
import sys
import time

INF = float('inf')


# ------------------------------------------------------------------ one bounce (the transcription of bounceM)
def norm(n0, G):
    """(n0', ms, r): the groups as the borrow sees them (lean: `norm`, an equality of tapes).  The borrow passes
    the groups (0, m+1); (0,0), (1,n) is one more x in the block before; (0,0), (0,0), (1,n) is the group (0, n+1)."""
    ms, G = [], list(G)
    while True:
        if G and G[0][0] == 0 and G[0][1] >= 1:
            ms.append(G[0][1] - 1)
            G = G[1:]
        elif len(G) >= 2 and G[0] == (0, 0) and G[1][0] == 1:
            if ms:
                ms[-1] += 1 + G[1][1]
            else:
                n0 += 1 + G[1][1]
            G = G[2:]
        elif len(G) >= 3 and G[0] == (0, 0) and G[1] == (0, 0) and G[2][0] == 1:
            ms.append(G[2][1])
            G = G[3:]
        else:
            return n0, ms, G


def after_dec(n0, ms, g, rest):
    if g == (0, 0) and rest and rest[0][0] == 1:
        n2, rest2 = rest[0][1], rest[1:]
        if not ms:
            return n0 + 1 + n2, rest2
        return n0, [(2, m) for m in ms[:-1]] + [(2, ms[-1] + 1 + n2)] + rest2
    return n0, [(2, m) for m in ms] + [g] + rest


def bounce_lean(n0, G):
    """('next', n0', G', event) | ('halt',).  Defined on every state (lean: `bounceM`, `bounceM_ne_stuck`).
    event: None (a decrement), 'E' / 'E0' (the round ends), 'D', 'A', 'F' (empty groups at the end),
    'M1' / 'M2' (a turn at one / two empty groups in front of a digit >= 2; none in the run so far)."""
    n0, ms, r = norm(n0, G)
    Z = [(0, m + 1) for m in ms]
    A = [(2, m) for m in ms]
    if not r:
        if not ms:
            return ('next', 0, [(1, n0), (0, 0)], 'E0')
        return ('next', 0, [(1, n0 + 1)] + Z[:-1] + [(0, ms[-1]), (0, 0)], 'E')
    (d, n), rest = r[0], r[1:]
    if d >= 1:
        return ('next',) + after_dec(n0 + 1, ms, (d - 1, n), rest) + (None,)
    if rest == []:
        return ('next', n0 + 1, A, 'D')
    if rest == [(0, 0)]:
        return ('next', n0 + 1, A + [(0, 0), (0, 0)], 'A')
    if rest == [(0, 0), (0, 0)]:
        return ('next', n0 + 1, A + [(1, 0)], 'F')
    d1, n1 = rest[0]
    if d1 >= 2:
        return ('next', 0, [(1, n0 + 1)] + Z + [(0, 0), (d1 - 2, n1)] + rest[1:], 'M1')
    if (d1, n1) != (0, 0):
        return ('halt',)                      # (0, n+1) after the empty group
    d2, n2 = rest[1]
    if d2 >= 2:
        return ('next', 0, [(1, n0 + 1)] + Z + [(0, 0), (0, 0), (d2 - 2, n2)] + rest[2:], 'M2')
    return ('halt',)                          # (0,0), (0, n+1), ...  or three empty groups and more


# ------------------------------------------------------------------ many bounces at once
def split_trailing(G):
    k = len(G)
    while k > 0 and G[k - 1] == (0, 0):
        k -= 1
    return G[:k], len(G) - k


def jump(n0, G):
    """(D, n0', G'): D >= 0 bounces at once, all of them plain decrements (no merge, no event)."""
    H, t = split_trailing(G)
    if t > 3:
        return 0, n0, G
    m = len(H)
    L = [0] * (m + 1)
    for i, (d, n) in enumerate(H):
        L[i + 1] = L[i] + d * 3 ** i
    best = INF if t == 2 else L[m]
    for i, (d, n) in enumerate(H):
        q = 3 ** (i + 1)
        if n >= 1:
            ev = L[i + 1] + 1 + (n - 1) * q          # the n-th pass of group i empties it
        else:
            ev = L[i + 1] + 1                         # the first pass of an empty block
            if d >= 1:
                ev = min(ev, L[i] + 1 + (d - 1) * 3 ** i)   # its digit reaches 0
        best = min(best, ev - 1)
    D = int(best)
    if D <= 0:
        return 0, n0, G
    newL = L[m] - D
    low = newL % 3 ** m if t == 2 else newL
    newH = []
    for i, (d, n) in enumerate(H):
        q = 3 ** (i + 1)
        newH.append(((low // 3 ** i) % 3, n - (L[m] // q - newL // q)))
    return D, n0 + D, newH + [(0, 0)] * t


START = (0, [(1, 5), (0, 0)])     # the counter at step 403 (lean/Model.lean, blank_to_counter)


def far(seconds):
    s, nb, rounds, t0, ev = START, 0, 0, time.time(), {}
    while time.time() - t0 < seconds:
        D, n0, G = jump(*s)
        nb += D
        r = bounce_lean(n0, G)
        nb += 1
        if r[0] != 'next':
            print(r[0].upper(), 'after', rounds, 'rounds', nb, 'bounces')
            return
        if r[3] in ('E0', 'M1', 'M2'):
            print('event', r[3], 'in round', rounds, s)
        s = (r[1], r[2])
        ev[r[3]] = ev.get(r[3], 0) + 1
        if r[3] in ('A', 'F'):
            print('event', r[3], 'in round', rounds, 'bounces ~10^%d' % (len(str(nb)) - 1), 'groups', len(s[1]))
        if r[3] == 'E':
            rounds += 1
            if rounds % 5000 == 0:
                print('round', rounds, 'bounces ~10^%d' % (len(str(nb)) - 1), 'groups', len(s[1]), ev)
                sys.stdout.flush()
    print('no halt: round', rounds, 'bounces ~10^%d' % (len(str(nb)) - 1), 'groups', len(s[1]), ev)


def check(path):
    prev, ok = None, 0
    for line in open(path):
        p = line.split()
        if len(p) < 3 or p[1] != 'C' or p[2] == '?':
            continue
        cur = (int(p[2]), [tuple(map(int, x.split(','))) for x in p[4:]][:-1])
        if prev is not None and prev[1] != []:   # (n0, []): cdump prints the intermediate visit of exhaust0 too
            r = bounce_lean(*prev)
            if r[0] == 'next' and (r[1], r[2]) == cur:
                ok += 1
            else:
                print('MISMATCH at step', p[0], prev, r, cur)
                return
        prev = cur
    print('all', ok, 'bounces agree with the model')


def enc(n0, G):
    s = '010' + '1110' * n0
    for d, n in G:
        s += '1' + '10' * d + '1110' * n
    return s + '1'


TABLE = "1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---"


def machine(n0, G, target, maxsteps=10 ** 6):
    """Run the machine from the counter configuration: 'halt', or 'ok' if it reaches the tape `target` with the
    head in C at the left end."""
    tr = {}
    for i, row in enumerate(TABLE.split('_')):
        for b in range(2):
            c = row[3 * b:3 * b + 3]
            tr[(chr(65 + i), b)] = None if c[0] == '-' else (int(c[0]), 1 if c[1] == 'R' else -1, c[2])
    tape = {i: int(c) for i, c in enumerate(enc(n0, G))}
    pos, st = 0, 'C'
    for _ in range(maxsteps):
        r = tr[(st, tape.get(pos, 0))]
        if r is None:
            return 'halt'
        tape[pos], pos, st = r[0], pos + r[1], r[2]
        if st == 'C' and tape.get(pos, 0) == 0:
            ones = [k for k, v in tape.items() if v]
            if min(ones) > pos and ''.join(str(tape.get(i, 0)) for i in range(pos, max(ones) + 1)) == target:
                return 'ok'
    return 'timeout'


def random_test(count):
    import random
    random.seed(1)
    kinds = {}
    for _ in range(count):
        G = [(random.choice([0, 0, 0, 1, 2, 2, 3]), random.choice([0, 0, 1, 2, 3])) for _ in range(random.randint(0, 6))]
        n0 = random.randint(0, 3)
        r = bounce_lean(n0, G)
        got = machine(n0, G, None if r[0] == 'halt' else enc(r[1], r[2]))
        if got != ('halt' if r[0] == 'halt' else 'ok'):
            print('MISMATCH', n0, G, r, got)
            return
        k = 'halt' if r[0] == 'halt' else str(r[3])
        kinds[k] = kinds.get(k, 0) + 1
    print('the model agrees with the machine on', count, 'random states:', kinds)


if __name__ == '__main__':
    if sys.argv[1] == 'far':
        far(float(sys.argv[2]))
    elif sys.argv[1] == 'random':
        random_test(int(sys.argv[2]))
    else:
        check(sys.argv[2])
