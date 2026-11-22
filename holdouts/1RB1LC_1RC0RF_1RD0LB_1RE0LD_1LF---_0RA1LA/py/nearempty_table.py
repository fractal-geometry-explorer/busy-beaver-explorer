"""The resets of 1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LF---_0RA1LA at a nearly empty tail, measured: for each suffix of the run
(`1001`, `1`, `1001101011001`), each r < 5 and each t below what row r of the reset table reads, the plain machine
from `0^inf B> 0 0 1 (1100)^n (10110110)^r 10 (1110)^t SUFFIX 0^inf`, n = 60..65, to the first clean record
(`c/nextrec.c`), or, when there is none within 3*10^8 steps, to the loop record `B> 0 0 1 (1100)^n' 0 1`
(`c/reset.c`).  This is the table that `lean/nearempty.py` proves for every n.

usage (from this folder):  gcc -O2 -o nextrec c/nextrec.c && gcc -O2 -o reset c/reset.c && python3 py/nearempty_table.py
"""
import subprocess

S2 = "1001101011001"
NEED = [4, 1, 4, 3, 2]


def tail(t, suf):
    return "10" + "1110" * t + suf


def first_record(n, r, T):
    return subprocess.run(["./nextrec", str(n), str(r), T, "1", "300000000"], capture_output=True, text=True).stdout.split()


def loop_record(n, r, T):
    for line in subprocess.run(["./reset", str(n), str(r), T, "400"], capture_output=True, text=True).stdout.splitlines():
        f = line.split()
        if len(f) == 4 and f[3] == "01":
            return int(f[0]), int(f[2])
    return None


def outcome(n, r, T):
    o = first_record(n, r, T)
    if o[0] == "HALT":
        return f"HALT at step {o[1]}"
    if o[0] == "TIMEOUT":
        lr = loop_record(n, r, T)
        return f"loop record n' = {lr[0]} at step {lr[1]}" if lr else "?"
    return f"(n', m') = ({o[0]}, {o[1]}) at step {o[2]}, then {' '.join(o[3:])}"


def main():
    for suf, label in [("01", "1001"), ("1", "1"), (S2, S2)]:
        for r in range(5):
            for t in ([0] if label == "1001" else range(NEED[r])):
                T = "1001" if label == "1001" else tail(t, suf)
                print(f"suffix {label}, r = {r}, t = {t}")
                for n in range(60, 66):
                    print(f"  n = {n}: {outcome(n, r, T)}")


if __name__ == "__main__":
    main()
