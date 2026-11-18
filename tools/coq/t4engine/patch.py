"""Patch the definitions of busycoq PR 93's engine (output of strip.py) for the T4 table.
usage: python3 patch.py engine93.v T4C.v
Each rep() names one site; the comment says which T3 rule it replaces by its T4 form."""
import sys
src=open(sys.argv[1]).read()
def rep(old,new,count=1):
    global src
    n=src.count(old)
    assert n==count,(n,old[:80])
    src=src.replace(old,new)
rep('"1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0RD---"','"1RB1RD_1LC0RE_1LD1LC_1RA0LB_0RD0RF_0LC---"')
rep('"1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0LB---"','"1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---"')
# collision calls (doCallsDSlow and doCallsD)
rep('pushD 2 1 (pushD 3 (hd - 1)%N (pushD (j + 1)%N 1 db1))','pushD 3 hd (pushD j 1 db1)',2)
# defect call
rep('pushD (m + 2)%N 1 (pushD (j + 1)%N 1 db1)','pushD (m + 3)%N 1 (pushD j 1 db1)')
# trySweepMR_a0: T4 versions of rule_mr_a0_* (checked by simulation, mra1.py)
rep("""  | (SW_DEF la lk, Npos pcl) :: lrest =>
    if N.leb 3 lk then""", """  | (SW_DEF la lk, Npos pcl) :: lrest =>
    if (if N.leb 1 la then N.leb 3 lk else false) then""")
rep('Some (pushS1 (m + 2)%N (pushDEF1 (la + 1)%N (lk - 3)%N l0))','Some (pushS1 (m + 3)%N (pushDEF1 la (lk - 3)%N l0))')
rep('Some (pushS1 (m + 2)%N (pushDEF1 (pln + 5)%N (2 * pln - 2)%N l0))','Some (pushS1 (m + 3)%N (pushDEF1 (pln + 4)%N (2 * pln - 2)%N l0))')
rep('Some (pushS1 (m + 2)%N (pushS1 (sn + 1)%N (pushDEF1 la (lk - 3)%N l0)))','Some (pushS1 (m + 3)%N (pushS1 sn (pushDEF1 la (lk - 3)%N l0)))')
rep('Some (pushS1 (m + 2)%N (pushS1 (sn + 1)%N (pushDEF1 (pln + 4)%N (2 * pln - 2)%N l0)))','Some (pushS1 (m + 3)%N (pushS1 sn (pushDEF1 (pln + 4)%N (2 * pln - 2)%N l0)))')
# stepMR_imm defect0D / defect0
rep('Some (MkFastState l (MkRTape [] [((m + 2)%N, 1%N)] [] (runs_push (SW_raw [1; 0]) 1 (unpackDFHead rt3))) MJ)',
    'Some (MkFastState l (MkRTape [] [((m + 3)%N, 1%N)] [] (runs_push (SW_raw [1; 0]) 1 (unpackDFHead rt3))) ML)')
rep('Some (MkFastState l (MkRTape [] [] [] (runs_push (SW_raw [1; 1; 1; 1]) 1 (runs_push (SW_D mv) 1 (runs_push (SW_raw [1]) 1 rt4)))) MJ)',
    'Some (MkFastState l (MkRTape [] [] [] (runs_push (SW_D (mv + 3)%N) 1 (runs_push (SW_raw [1]) 1 rt4))) ML)')
# handleDefInSweep rem 0 cases (def_k0_ML)
rep('if N.eqb rem 0 then DSR_done true (pushD a 1 df) db rtail','if N.eqb rem 0 then DSR_done false (pushD (a + 1)%N 1 df) db rtail')
rep("if N.eqb rem 0 then DSR_done true (pushD a 1 df') db' rtail'","if N.eqb rem 0 then DSR_done false (pushD (a + 1)%N 1 df') db' rtail'")
rep("if N.eqb rem 0 then DSR_done true (pushD (a + 1)%N 1 df') db' rtail'","if N.eqb rem 0 then DSR_done false (pushD (a + 2)%N 1 df') db' rtail'")
# sweepLeftBlankDef1
rep("if N.eqb rem 0 then (true, pushD a 1 df, db')","if N.eqb rem 0 then (false, pushD (a + 1)%N 1 df, db')")
rep("if N.eqb rem 0 then (true, pushD (a + 1)%N 1 df, db')","if N.eqb rem 0 then (false, pushD (a + 2)%N 1 df, db')")
# PL returns in sweepLeftOne
rep('''            let df'' :=
              if negb isMJ then pushD d6 (mc - 1)%N (pushD (5 + n * 3)%N 1 df')
              else pushD d6 mc df' in
            SLS_cont true true l' df'' db' rtail\'''','''            let df'' :=
              if negb isMJ then pushD d6 mc df'
              else pushD d6 (mc - 1)%N (pushD (7 + n * 3)%N 1 df') in
            SLS_cont true false l' df'' db' rtail\'''')
rep('''      let df'' :=
        if negb isMJ then pushD d6 (N.pred cnt1) (pushD (5 + n * 3)%N 1 df)
        else pushD d6 cnt1 df in
      sweepLeftBlank rest true true df'' (pushD 0 (mul2 req) db)''','''      let df'' :=
        if negb isMJ then pushD d6 cnt1 df
        else pushD d6 (N.pred cnt1) (pushD (7 + n * 3)%N 1 df) in
      sweepLeftBlank rest true false df'' (pushD 0 (mul2 req) db)''')
# stepML_col
rep("Some (MkFastState l' (MkRTape [] (pushD (dn + 2)%N 1 (d_front rt1)) (d_back rt1) (r_tail rt1)) MJ)",
    "Some (MkFastState l' (MkRTape [] (pushD (dn + 3)%N 1 (d_front rt1)) (d_back rt1) (r_tail rt1)) ML)")
rep("Some (MkFastState l' (MkRTape (runs_push (SW_raw [1; 1; 1; 1]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) MJ)",
    "Some (MkFastState l' (MkRTape (runs_push (SW_raw [1; 1; 1; 1; 1; 1]) 1 (r_raw rt)) (d_front rt) (d_back rt) (r_tail rt)) ML)")
hdr='''From BusyCoq Require Import Individual62.
Require Import List PeanoNat NArith PArith ZifyNat Lia String.
Import ListNotations.
Open Scope list_scope.
Open Scope sym_scope.
'''
inf='Local Infix "/" := Nat.div : nat_scope.\nLocal Infix "mod" := Nat.modulo (at level 40, no associativity) : nat_scope.\n'
a='(TM_from_str "1RB1RA_1LC0RD_1LD1LB_1RA0LE_0LB0LF_0RA---").\n'
src=src.replace(a,a+'Local Notation "c -->* c\'" := (c -[ src_tm ]->* c\') (at level 40).\n',1)
extra=open(__file__.rsplit('/',1)[0]+'/extra.v' if '/' in __file__ else 'extra.v').read()
open(sys.argv[2],'w').write(hdr+'\nModule T4C.\n'+inf+src+'\n'+extra+'\nEnd T4C.\n')
