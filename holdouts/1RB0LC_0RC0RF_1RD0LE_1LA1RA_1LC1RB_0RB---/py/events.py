"""The E-events of 1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB--- (partial analysis).

Sample the run when the head is in state E at the left end of the tape.  The tape is then a list of blocks,

    E> (10)^2 (0100)^189 (10)^3 (0010)^633 (01)^2 (0001)^n  tail

in which all blocks but the last are frozen and the last one grows by a factor of about 1.4 per event (n = 13, 159,
363, 649, 1050, 1612, 2398, 3499, 5039, 7197, 10215, 14443, 20361, 28645, 40230), with a short tail that changes from
event to event.  Earlier blocks were the growing block of a previous level (0100 up to 189 copies, then 0010 up to
633).  During one pass the head sweeps the whole tape, moving 14 copies at a time out of the middle block and back.
At step 1.9e10 a new level seems to start: the tail becomes 0^2 (10)^2 (0010)^7 0^2 1^2.

usage: python3 events.py STEPS          print the compressed E-events of the blank run
"""
import os, sys

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..",
                                "1RB0LA_0RC0RB_1LD1LA_1LC1RE_1RF0RD_1LC---", "py"))
import g01tools as g  # noqa: E402

M = "1RB0LC_0RC0RF_1RD0LE_1LA1RA_1LC1RB_0RB---"

if __name__ == "__main__":
    for k, t in g.events(M, "A> 0", int(float(sys.argv[1])), "E", "L"):
        if isinstance(t, int):
            print(k, t)
            break
        print(k, g.show(t)[:200], flush=True)
