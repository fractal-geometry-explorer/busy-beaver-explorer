"""Build H155900.v, the Coq proof that 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD--- halts, from DeepMind's PR 93 file.
usage: mk.py OUT.v M_1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RDHHH.v [fast]   (fast admits the final evaluation)"""
import re,sys
import os
HERE=os.path.dirname(os.path.abspath(__file__))
src=open(sys.argv[2]).read()
P=open(os.path.join(HERE,'..','patch.py')).read()
body=P[P.index('def rep('):P.index('hdr=')]
def rep(old,new,count=1):
    global src
    n=src.count(old); assert n==count,(n,old[:90]); src=src.replace(old,new)
lines=body.split('\n')
# drop the rep() definition itself and the two table replacements
code='\n'.join(l for l in lines if 'TM_from_str' not in l and '"1RB1RD_1LC0RE' not in l and '"1RB1RA_1LC0RD' not in l)
code=code[code.index('\n', code.index('src=src.replace(old,new)'))+1:]
exec(code)
rep('Definition tm : TM := TM_from_str "1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---".','Definition tm : TM := TM_from_str "1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD---".')
rep('(TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---")','(TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---")')
rep('  | A => C | B => D | C => A | D => B | E => E | F => F','  | A => D | B => A | C => B | D => C | E => E | F => F')
rep('Lemma halts_iso : halts src_tm (C;; tape0) -> halts tm c0.','Lemma halts_iso : halts src_tm (B;; tape0) -> halts tm c0.')
rep('change (flip_conf (C;; tape0)) with (C;; tape0) in H.','change (flip_conf (B;; tape0)) with (B;; tape0) in H.')
src=src.replace('Module M598.','Module H155900.').replace('End M598.','End H155900.').replace('M598.','H155900.')
src=src.replace('Definition initFastC : FastState := MkFastState [] (MkRTape [] [] [] []) (RAW C R).','Definition initFastB : FastState := MkFastState [] (MkRTape [] [] [] []) (RAW B R).')
src=src.replace('initFastC','initFastB').replace('(C;; tape0)','(B;; tape0)').replace('run_pow 22','run_pow 19').replace('run_pow_spec 22','run_pow_spec 19')
if len(sys.argv)>3 and sys.argv[3]=='fast': src=src.replace('Proof. vm_check_eq. Qed.','Admitted.')
src=src.rstrip('\n')+'\n\nPrint Assumptions halt.\n'
open(sys.argv[1],'w').write(src)
