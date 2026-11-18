"""Compare the block-list runs of an F05 start-A machine and its start-C twin at every left-end event.

The two machines have the same frame-A table; one starts in A, the other in C.  From the fourth left-end event on
(index 3), the start-C run's block list should be the start-A run's with the first block 16 longer.  This runs both
with the exact block-list map (`f05_run.run`: hybrid.py or hybrid2.py) to STEPS steps and reports the first left-end
event where that fails, if any, and whether the F-events agree in number.

usage: python3 start_twins_check.py X Y [STEPS=1e200]     # X the start-A machine, Y the start-C machine
"""
import sys
import f05_run


def compare(x, y, n):
    hx, _, sx = f05_run.run(x, n)
    hy, _, sy = f05_run.run(y, n)
    tx, ty = hx.top, hy.top
    k = min(len(tx), len(ty))
    first_bad = None
    for i in range(3, k):
        a, c = tx[i][2], ty[i][2]
        if not (len(a) == len(c) and a[1:] == c[1:] and c[0] - a[0] == 16):
            first_bad = i
            break
    return dict(events=(len(tx), len(ty)), f_events=(len(hx.fev), len(hy.fev)), compared=k,
                first_bad=first_bad, bad_step=None if first_bad is None else tx[first_bad][0],
                bad_lists=None if first_bad is None else (tx[first_bad - 1][2][:4], tx[first_bad][2][:4], ty[first_bad][2][:4]),
                last_step_digits=len(str(tx[k - 1][0])), halted=(hx.halted, hy.halted), secs=round(sx + sy))


if __name__ == "__main__":
    x, y = sys.argv[1], sys.argv[2]
    n = float(sys.argv[3]) if len(sys.argv) > 3 else 1e200
    print(x, y, compare(x, y, n), flush=True)
