"""Run 1RB1RF_1LC0LA_---0LD_1LE1RB_0RA0LB_1RE0RE from blank tape with bbtools.cycles on 6-cell blocks.

Every jump of the accelerator is k applications of a cycle rule proved with bbtools.symtm (the rules used up to
10^9 steps are lean/Cycles.lean).  Prints the macro tape each time its shape (the words, not the counts) changes
at a visit of the right end, and with `lean OUT` writes the Lean file of the rules used.

usage: python3 cycles_run.py 1e12 > shapes.txt            (about 10 minutes)
       python3 cycles_run.py 1e9 lean ../lean/Cycles.lean
"""
import os, re, sys, time
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', '..', 'tools', 'py'))
from bbtools.cycles import Accelerator, at_tape_end
from bbtools.macro import MacroRun

M = '1RB1RF_1LC0LA_---0LD_1LE1RB_0RA0LB_1RE0RE'


def main():
    n = int(float(sys.argv[1]))
    last = [None]

    def sample(r):
        e = at_tape_end(r)
        if e and r.dir == 1:
            s = str(r)
            sh = re.sub(r'\^\d+', '', s)
            if sh != last[0]:
                print(r.steps, s, flush=True)
                last[0] = sh
        return e
    t0 = time.time()
    a = Accelerator(MacroRun(M, 6), sample=sample).run(n)
    r = a.run_
    print('halted' if r.halted else 'no halt', 'at', r.steps, 'steps;', len(a.rules), 'rules,', len(a.jumps), 'jumps,',
          round(time.time() - t0), 's')
    if len(sys.argv) > 3 and sys.argv[2] == 'lean':
        txt = a.lean_file('Machine', 'H12189', doc=f'Cycle rules of {M} proved by bbtools.cycles (blocks of 6 '
                          f'cells), the ones used in the first {n:.0e} steps from blank tape.')
        txt = txt.replace('open TM\n', 'open TM\n\nset_option maxRecDepth 20000\n', 1)
        open(sys.argv[3], 'w').write(txt)


if __name__ == '__main__':
    main()
