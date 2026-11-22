"""Write lean/MoverRules.lean: the cell-level rules for the head crossing one mover, and for Q turning the head
round with an unknown tape R on its right, proved by bbtools.symtm.prove.  Run: python3 holdouts/<M>/py/gen_movers.py

At rest (the head at the right end, about to turn left) a mover is the word `0 0 1 1 0` followed by g pairs `01`.
The left sweep (state E, reading a 0) crosses it and leaves it as `0 1 0 1 1 (01)^g` one cell further right
(`lm`); the right sweep (state D) crosses that and leaves `1 0 1 | 0 0 1 1 0 (01)^(g-2) 0` (`rm`): the mover has
moved four cells to the right and the head comes out in the state it went in.  After a mover with a one-pair gap
the head is in state F instead (`rm1`, `fm1`), and the next longer gap brings it back to D (`fm`); the movers move
the same way.  `qr0`, `qr1`: the left sweep
reaches Q (an extra 0 or 1 in the pairs) and comes back in state D.  `endb`: the right sweep at the blank end."""
import os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, "../../../tools/py"))
from bbtools.symtm import prove, rules_file

M = os.path.basename(os.path.dirname(HERE))
RULES = [
    ("lm_cells", "L 0 0 1 1 0 (01)^n+1 E> 0 R", "L E> 0 0 1 0 1 1 (01)^n+1 R",
     "The left sweep crosses a mover at rest: `L 0 0 1 1 0 (01)^(n+1) E> 0 R` becomes `L E> 0 0 1 0 1 1 (01)^(n+1) R`."),
    ("rm_cells", "L D> 0 1 0 1 1 (01)^n+2 R", "L 1 0 1 0 0 1 1 0 0 (10)^n D> R",
     "The right sweep crosses a swept mover: `L D> 0 1 0 1 1 (01)^(n+2) R` becomes `L 1 0 1 0 0 1 1 0 0 (10)^n D> R`."),
    ("rm1_cells", "L D> 0 1 0 1 1 0 1 R", "L 1 0 1 0 0 1 1 F> R",
     "The right sweep crosses a swept mover with a one-pair gap and comes out in state F."),
    ("fm1_cells", "L F> 0 1 0 1 1 0 1 R", "L 0 0 1 0 0 1 1 F> R",
     "In state F the right sweep crosses a swept mover with a one-pair gap and stays in F."),
    ("fm_cells", "L F> 0 1 0 1 1 (01)^n+2 R", "L 0 0 1 0 0 1 1 0 0 (10)^n D> R",
     "In state F the right sweep crosses a swept mover with a longer gap and comes out in state D."),
    ("qr0_cells", "L (01)^c+1 0 (01)^a+1 E> 0 R", "L (01)^c 1 0 1 0 (10)^a+1 D> R",
     "The left sweep turns at Q in its short form, whatever lies on the right."),
    ("qr1_cells", "L (01)^c+1 1 (01)^a+1 E> 0 R", "L (01)^c 0 0 1 0 (10)^a+1 D> R",
     "The left sweep turns at Q in its long form, whatever lies on the right."),
]
ths = [prove(M, name, s, e, doc=doc)[0] for name, s, e, doc in RULES]
out = rules_file("Machine", "H71372", ths, "Mover rules of " + M + ", written by `py/gen_movers.py` with `bbtools.symtm.prove`.")
open(os.path.join(HERE, "../lean/MoverRules.lean"), "w").write(out)
print("wrote lean/MoverRules.lean")
