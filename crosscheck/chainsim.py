"""Independent accelerated simulator (Marxen-Buntrock style block macro machine with chain steps), written for
the cross-check. The tape is two stacks of (block, count) runs, counts are Python big integers. A chain step
crosses a whole run of identical blocks at once when the macro transition keeps the state and direction.
It is exact: every reported step count is the true number of base steps (the halting step included).
usage: python3 chainsim.py TNF K MACROSTEPS [SECONDS]"""
import sys, time
from tnf import parse

def run(name, k, max_macro, seconds=1e9):
    t = parse(name)
    cache = {}
    def macro(q, d, blk):
        """Run the base machine on one block of k cells, entering from the left (d='R') or right (d='L').
        Returns (new_block, new_state, exit_dir, steps) or ('halt', steps, (q,b)) or None (stays inside > bound)."""
        key = (q, d, blk)
        if key in cache: return cache[key]
        cells = list(blk); pos = 0 if d == "R" else k - 1; steps = 0; seen = set()
        while 0 <= pos < k:
            st = (q, pos, tuple(cells))
            if st in seen: cache[key] = None; return None   # loops inside the block forever
            seen.add(st)
            tr = t[(q, cells[pos])]
            if tr is None:
                cache[key] = ("halt", steps + 1, (q, cells[pos]), tuple(cells), pos); return cache[key]
            w, mv, nq = tr; cells[pos] = w; pos += 1 if mv == "R" else -1; q = nq; steps += 1
        res = (tuple(cells), q, "R" if pos >= k else "L", steps)
        cache[key] = res; return res
    zero = (0,) * k
    left, right = [], []          # stacks of [block, count]; top = nearest the head; beyond: zero blocks
    q, d = "A", "R"               # head is between the two stacks, about to enter the next block on side d
    steps = 0; t0 = time.time()
    def pop(stack):
        if not stack: return zero, 1
        b, n = stack[-1]
        if n == 1: stack.pop()
        else: stack[-1][1] = n - 1
        return b, 1
    def push(stack, b, n):
        if stack and stack[-1][0] == b: stack[-1][1] += n
        elif not stack and b == zero: return
        else: stack.append([b, n])
    for i in range(max_macro):
        src, dst = (right, left) if d == "R" else (left, right)
        if src: b, n = src[-1]
        else: b, n = zero, 1
        r = macro(q, d, b)
        if r is None: return ("loop", steps, i)
        if r[0] == "halt":
            ones = sum(sum(bb) * nn for bb, nn in left + right) - sum(b) + sum(r[3])
            return ("halt", steps + r[1], r[2], ones, i)
        nb, nq, nd, s = r
        if nq == q and nd == d and src:      # chain step: cross the whole run
            src.pop(); push(dst, nb, n); steps += s * n
        else:
            pop(src); steps += s
            if nd == d: push(dst, nb, 1)
            else: push(src, nb, 1)
        q, d = nq, nd
        if (i & 0xffff) == 0 and time.time() - t0 > seconds: return ("timeout", steps, i)
    return ("budget", steps, max_macro)

if __name__ == "__main__":
    name, k, m = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    sec = float(sys.argv[4]) if len(sys.argv) > 4 else 1e9
    print(run(name, k, m, sec))
