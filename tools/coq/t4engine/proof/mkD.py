"""Turn H155900.v (T4 started in B) into H67137.v: 1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB--- halts.
That machine is T4 renamed (A->B, B->C, C->D, D->A), not mirrored, started in state D. The engine needs
688,228 fast steps from D, so the final run is run_pow 20 instead of 19.
usage: mkD.py H155900.v OUT.v [fast]"""
import sys
s = open(sys.argv[1]).read()
def rep(a, b, count=1):
    global s
    n = s.count(a); assert n == count, (n, a[:80]); s = s.replace(a, b)
rep('Definition tm : TM := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---".',
    'Definition tm : TM := TM_from_str "1RB0LE_1RC1RB_1LD0RA_1LA1LC_0LC0LF_0RB---".')
rep('  | A => D | B => A | C => B | D => C | E => E | F => F', '  | A => B | B => C | C => D | D => A | E => E | F => F')
rep('Lemma perm_src : Perm (flip src_tm) tm permState.', 'Lemma perm_src : Perm src_tm tm permState.')
rep('''  intros H.
  apply flip_halts in H.
  change (flip_conf (B;; tape0)) with (B;; tape0) in H.
  exact''', '''  intros H.
  exact''')
s = s.replace('Module H155900.', 'Module H67137.').replace('End H155900.', 'End H67137.').replace('H155900.', 'H67137.')
rep('MkFastState [] (MkRTape [] [] [] []) (RAW B R)', 'MkFastState [] (MkRTape [] [] [] []) (RAW D R)')
s = s.replace('initFastB', 'initFastD')
n = s.count('(B;; tape0)'); assert n >= 3, n
s = s.replace('(B;; tape0)', '(D;; tape0)')
n = s.count('run_pow 19'); assert n >= 2, n
s = s.replace('run_pow 19', 'run_pow 20').replace('run_pow_spec 19', 'run_pow_spec 20')
if len(sys.argv) > 3 and sys.argv[3] == 'fast':
    rep('Lemma run_ok : is_none (run_pow 20 initFastD) = true.\nProof. vm_check_eq. Qed.',
        'Lemma run_ok : is_none (run_pow 20 initFastD) = true.\nAdmitted.')
open(sys.argv[2], 'w').write(s)
