"""Write lean/Rules.lean: whole sweeps of 1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE for the generic parity patterns,
proved by bbtools.symtm.prove for all block lengths.  Run from anywhere: python3 holdouts/<M>/py/gen_rules.py

Notation.  At the start of a sweep (B on the blank cell right of the tape) the tape is
    0^inf (10)^n1 0 (10)^n2 0 ... 0 (10)^nk 1 B>0
a list of blocks of `10`s, each followed by one extra 0, the last one (the youngest, the sweep counter) ending in a
bare 1.  Its *count* is the number of 1s in it: n_i for an inner block, n_k + 1 for the last.  A block of count
2x+4 is written (1010)^x+2 0, of count 2x+5 (1010)^x+2 1 0 0; the last block of count 2c+5 is (1010)^c+2 1, of
count 2c+6 (1010)^c+2 1 0 1.  The rules say what one sweep (B at the right end to B at the right end) does to the
counts nearest the right end; L, the rest of the tape to the left, is not looked at.
"""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools import symtm
from bbtools.symtm import prove, rules_file, Config, Blank
from bbtools.machine import Machine

M = "1RB0RA_1LC0RA_0LF0LD_1LE---_0LC0LB_1LA0RE"
m = Machine.parse(M)
INNER = {"E": "(1010)^{v}+2 0", "O": "(1010)^{v}+2 1 0 0"}
LAST = {"O": "(1010)^c+2 1 B> 0^inf", "E": "(1010)^c+2 1 0 1 B> 0^inf"}


def start(last, inner):
    """inner: parities of the inner blocks, nearest the right end first; variables y1, y2, ..."""
    parts = ["L"] + [INNER[p].format(v=f"y{i + 1}") for i, p in reversed(list(enumerate(inner)))] + [LAST[last]]
    return " ".join(parts)


def run_to_end(s):
    cfg = Config.parse(s)
    for i in range(100000):
        if i and cfg.state == 1 and isinstance(cfg.right[-1], Blank) and all(t == 0 for t in cfg.right[:-1]):
            return cfg
        x = symtm.try_cross(m, cfg)
        if x is None:
            c2 = cfg.copy()
            if symtm.try_rotate(c2) is not None and symtm.try_cross(m, c2) is not None:
                cfg = c2
                continue
            symtm.step(m, cfg)
    raise RuntimeError(s)


def count(p, v):
    return f"2{v}+{4 if p == 'E' else 5}"


# (name, parity of the last block, parities of the inner blocks nearest first, change of the counts, last first)
FAMILIES = [
    ("sweep_E_OE", "E", "OE", "(+1, +1, -1)"),
    ("sweep_E_OO", "E", "OO", "(+1, +1, -1)"),
    ("sweep_E_EEE", "E", "EEE", "(+1, -1, +2, -1)"),
    ("sweep_E_EEO", "E", "EEO", "(+1, -1, +2, -1)"),
    ("sweep_E_EOEE", "E", "EOEE", "(+1, -1, 0, +2, -1)"),
    ("sweep_E_EOEO", "E", "EOEO", "(+1, -1, 0, +2, -1)"),
    ("sweep_O_EEEE", "O", "EEEE", "(+1, 0, 0, +1, -1)"),
    ("sweep_O_EEEO", "O", "EEEO", "(+1, 0, 0, +1, -1)"),
    ("sweep_O_EOOE", "O", "EOOE", "(+1, 0, 0, +1, -1)"),
    ("sweep_O_EEOEE", "O", "EEOEE", "(+1, 0, 0, -1, +2, -1)"),
]
def main():
  ths = []
  for name, last, inner, change in FAMILIES:
      s = start(last, inner)
      fin = run_to_end(s)
      counts = ", ".join([("2c+6" if last == "E" else "2c+5")] + [count(p, f"y{i + 1}") for i, p in enumerate(inner)])
      doc = (f"A sweep with counts ({counts}) (the last block first, then the inner blocks leftwards): "
             f"the counts change by {change}.  Start `{s}`, end `{fin}`.")
      ths.append(prove(M, name, s, str(fin), doc=doc, max_moves=20000, max_seg=30, count_first=True)[0])
      print(name, fin.steps)
  out = rules_file("Machine", "H142609", ths, "Whole sweeps of " + M + " for generic block lengths, written by "
                   "`py/gen_rules.py` with `bbtools.symtm.prove`.")
  open(os.path.join(HERE, "../lean/Rules.lean"), "w").write(out)
  print("wrote lean/Rules.lean")


if __name__ == "__main__":
    main()
