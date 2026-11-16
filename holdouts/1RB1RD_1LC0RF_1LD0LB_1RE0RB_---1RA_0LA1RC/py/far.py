"""far.py MACHINE SECONDS: the accelerated run from blank tape for SECONDS seconds; a line every 500 bits of the step
count (exact big integers).  Prints `halted` with the step count if the machine halts."""
import sys,time
from cyc import *
sys.set_int_max_str_digits(0)
M=sys.argv[1]; TL=float(sys.argv[2])
a=Sim(M); ac=Acc(a); t0=time.time(); nb=20
while ac.step():
    if a.steps.bit_length()>=nb:
        print(f"2^{nb} steps: macro {a.nmacro} jumps {ac.njump} rules {sum(map(len,ac.rules.values()))} fails {len(ac.fail)} entries {len(a.L)+len(a.R)} t={time.time()-t0:.1f}",flush=True); nb+=500
    if a.nmacro%1000==0 and time.time()-t0>TL: break
print("halted" if a.halted else ("forever" if ac.forever else "timeout"), "steps",a.steps if a.steps<10**40 else "2^%d"%a.steps.bit_length())
print(show(a)[:600])
