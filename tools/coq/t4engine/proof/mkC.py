"""Turn H155900.v (T4 started in B) into H127983.v: 1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC--- halts.
That machine is T4 mirrored and renamed (A->C, B->D, C->A, D->B), started in state C.
usage: mkC.py H155900.v OUT.v [fast]"""
import sys
s = open(sys.argv[1]).read()
def rep(a, b, count=1):
    global s
    n = s.count(a); assert n == count, (n, a[:80]); s = s.replace(a, b)
rep('Definition tm : TM := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---".',
    'Definition tm : TM := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---".')
rep('  | A => D | B => A | C => B | D => C | E => E | F => F', '  | A => C | B => D | C => A | D => B | E => E | F => F')
s = s.replace('Module H155900.', 'Module H127983.').replace('End H155900.', 'End H127983.').replace('H155900.', 'H127983.')
rep('MkFastState [] (MkRTape [] [] [] []) (RAW B R)', 'MkFastState [] (MkRTape [] [] [] []) (RAW C R)')
s = s.replace('initFastB', 'initFastC')
n = s.count('(B;; tape0)'); assert n >= 4, n
s = s.replace('(B;; tape0)', '(C;; tape0)')
if len(sys.argv) > 3 and sys.argv[3] == 'fast':
    s = s.replace('Lemma run_ok : is_none (run_pow 19 initFastC) = true.\nProof. vm_check_eq. Qed.',
                  'Lemma run_ok : is_none (run_pow 19 initFastC) = true.\nAdmitted.')
open(sys.argv[2], 'w').write(s)
