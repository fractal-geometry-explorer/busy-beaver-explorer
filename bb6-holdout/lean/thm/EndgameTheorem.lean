import EndgamePieces0
import EndgamePieces1
import EndgamePieces2
import EndgamePieces3
open BB6 BB6.Sym

/-! # The endgame as a theorem

The phase-0 pass starts with R ≥ 178 form one class, with R a coordinate (`symStart`); for each even R < 178 outside
the closing set, the pass starts with that R form a class (`startR R`).  A tree of coordinate splits and skews for each
class (built by the untrusted program `ExploreNC.lean`, so it covers the class by construction; `adv` nodes run the
rounds before a split once for the whole subtree) is checked by the proved function `Tree.okNC`, evaluated by the
kernel (`decide +kernel`; no compiler is trusted).  The checks are cut into subtrees with a theorem each, in the
modules `EndgamePieces0`, … (compiled in parallel), and assembled here by `Tree.okNC_node` and `Tree.okNC_skew`.
`endgame_no_close` is the statement for the machine. -/

/-- The tree for every R ≥ 178. -/
def symTree : Tree := (.node 3 (.skew 1 2 1 (.node 1 egSymP0 (.node 2 (.skew 1 2 1 (.node 1 egSymP1 (.node 3 (.skew 1 2 1 (.node 1 egSymP2 (.skew 1 2 1 (.node 1 egSymP3 (.node 3 (.skew 1 2 1 (.node 1 (.node 3 (.node 1 (.node 3 egSymP4 (.node 1 (.node 3 (.skew 1 3 1 (.node 1 egSymP5 egSymP6)) egSymP7) (.node 1 (.skew 2 3 1 (.node 2 (.node 3 egSymP8 egSymP9) egSymP10)) egSymP11))) egSymP12) (.node 1 (.node 3 (.skew 1 2 1 (.node 1 egSymP13 egSymP14)) (.skew 1 2 1 (.node 1 egSymP15 (.node 3 egSymP16 egSymP17)))) egSymP18)) egSymP19)) (.skew 1 2 1 (.node 1 egSymP20 (.node 3 (.skew 1 2 1 (.node 1 egSymP21 egSymP22)) (.skew 1 2 1 (.node 1 egSymP23 egSymP24)))))))))) (.skew 1 2 1 (.node 1 (.node 3 egSymP25 egSymP26) (.node 1 egSymP27 (.skew 2 3 1 (.node 2 (.node 3 egSymP28 egSymP29) egSymP30)))))))) egSymP31))) egSymP32)

theorem sym_tree_ok : symTree.okNC 448 1000 4 false symStart.1 symStart.2.1 symStart.2.2 = true :=
  (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP1_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP3_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) egSymP4_ok (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP5_ok egSymP6_ok)) egSymP7_ok) (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) egSymP8_ok egSymP9_ok) egSymP10_ok)) egSymP11_ok))) egSymP12_ok) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP13_ok egSymP14_ok)) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP15_ok (Tree.okNC_node (by decide) egSymP16_ok egSymP17_ok)))) egSymP18_ok)) egSymP19_ok)) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP20_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP21_ok egSymP22_ok)) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egSymP23_ok egSymP24_ok)))))))))) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) egSymP25_ok egSymP26_ok) (Tree.okNC_node (by decide) egSymP27_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) egSymP28_ok egSymP29_ok) egSymP30_ok)))))))) egSymP31_ok))) egSymP32_ok)

def egTree6 : Tree := egR6P0

theorem egTree6_ok : egTree6.okNC 448 1000 3 false (startR 6).1 (startR 6).2.1 (startR 6).2.2 = true :=
  egR6P0_ok

def egTree10 : Tree := egR10P0

theorem egTree10_ok : egTree10.okNC 448 1000 3 false (startR 10).1 (startR 10).2.1 (startR 10).2.2 = true :=
  egR10P0_ok

def egTree12 : Tree := (.skew 1 2 1 (.node 1 egR12P0 (.node 2 (.skew 1 2 1 (.node 1 egR12P1 (.skew 1 2 1 (.node 1 egR12P2 (.node 1 egR12P3 (.node 2 egR12P4 egR12P5)))))) egR12P6)))

theorem egTree12_ok : egTree12.okNC 448 1000 3 false (startR 12).1 (startR 12).2.1 (startR 12).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR12P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR12P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR12P2_ok (Tree.okNC_node (by decide) egR12P3_ok (Tree.okNC_node (by decide) egR12P4_ok egR12P5_ok)))))) egR12P6_ok)))

def egTree14 : Tree := egR14P0

theorem egTree14_ok : egTree14.okNC 448 1000 3 false (startR 14).1 (startR 14).2.1 (startR 14).2.2 = true :=
  egR14P0_ok

def egTree18 : Tree := egR18P0

theorem egTree18_ok : egTree18.okNC 448 1000 3 false (startR 18).1 (startR 18).2.1 (startR 18).2.2 = true :=
  egR18P0_ok

def egTree20 : Tree := (.skew 1 2 1 (.node 1 egR20P0 (.node 2 (.skew 1 2 1 (.node 1 egR20P1 (.skew 1 2 1 (.node 1 egR20P2 egR20P3)))) egR20P4)))

theorem egTree20_ok : egTree20.okNC 448 1000 3 false (startR 20).1 (startR 20).2.1 (startR 20).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR20P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR20P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR20P2_ok egR20P3_ok)))) egR20P4_ok)))

def egTree22 : Tree := egR22P0

theorem egTree22_ok : egTree22.okNC 448 1000 3 false (startR 22).1 (startR 22).2.1 (startR 22).2.2 = true :=
  egR22P0_ok

def egTree26 : Tree := egR26P0

theorem egTree26_ok : egTree26.okNC 448 1000 3 false (startR 26).1 (startR 26).2.1 (startR 26).2.2 = true :=
  egR26P0_ok

def egTree28 : Tree := (.skew 1 2 1 (.node 1 egR28P0 (.node 2 (.skew 1 2 1 (.node 1 egR28P1 (.skew 1 2 1 (.node 1 egR28P2 (.node 1 egR28P3 (.node 2 egR28P4 egR28P5)))))) egR28P6)))

theorem egTree28_ok : egTree28.okNC 448 1000 3 false (startR 28).1 (startR 28).2.1 (startR 28).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR28P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR28P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR28P2_ok (Tree.okNC_node (by decide) egR28P3_ok (Tree.okNC_node (by decide) egR28P4_ok egR28P5_ok)))))) egR28P6_ok)))

def egTree30 : Tree := egR30P0

theorem egTree30_ok : egTree30.okNC 448 1000 3 false (startR 30).1 (startR 30).2.1 (startR 30).2.2 = true :=
  egR30P0_ok

def egTree34 : Tree := egR34P0

theorem egTree34_ok : egTree34.okNC 448 1000 3 false (startR 34).1 (startR 34).2.1 (startR 34).2.2 = true :=
  egR34P0_ok

def egTree36 : Tree := (.skew 1 2 1 (.node 1 egR36P0 (.node 2 (.skew 1 2 1 (.node 1 egR36P1 (.skew 1 2 1 (.node 1 egR36P2 egR36P3)))) egR36P4)))

theorem egTree36_ok : egTree36.okNC 448 1000 3 false (startR 36).1 (startR 36).2.1 (startR 36).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR36P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR36P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR36P2_ok egR36P3_ok)))) egR36P4_ok)))

def egTree38 : Tree := egR38P0

theorem egTree38_ok : egTree38.okNC 448 1000 3 false (startR 38).1 (startR 38).2.1 (startR 38).2.2 = true :=
  egR38P0_ok

def egTree40 : Tree := (.skew 1 2 1 (.node 1 egR40P0 (.node 2 (.skew 1 2 1 (.node 1 egR40P1 (.skew 1 2 1 (.node 1 egR40P2 (.skew 1 2 1 (.node 1 egR40P3 egR40P4)))))) egR40P5)))

theorem egTree40_ok : egTree40.okNC 448 1000 3 false (startR 40).1 (startR 40).2.1 (startR 40).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR40P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR40P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR40P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR40P3_ok egR40P4_ok)))))) egR40P5_ok)))

def egTree42 : Tree := egR42P0

theorem egTree42_ok : egTree42.okNC 448 1000 3 false (startR 42).1 (startR 42).2.1 (startR 42).2.2 = true :=
  egR42P0_ok

def egTree44 : Tree := (.skew 1 2 1 (.node 1 egR44P0 (.node 2 (.skew 1 2 1 (.node 1 egR44P1 (.skew 1 2 1 (.node 1 egR44P2 (.node 1 egR44P3 (.node 2 egR44P4 egR44P5)))))) egR44P6)))

theorem egTree44_ok : egTree44.okNC 448 1000 3 false (startR 44).1 (startR 44).2.1 (startR 44).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR44P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR44P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR44P2_ok (Tree.okNC_node (by decide) egR44P3_ok (Tree.okNC_node (by decide) egR44P4_ok egR44P5_ok)))))) egR44P6_ok)))

def egTree46 : Tree := egR46P0

theorem egTree46_ok : egTree46.okNC 448 1000 3 false (startR 46).1 (startR 46).2.1 (startR 46).2.2 = true :=
  egR46P0_ok

def egTree50 : Tree := egR50P0

theorem egTree50_ok : egTree50.okNC 448 1000 3 false (startR 50).1 (startR 50).2.1 (startR 50).2.2 = true :=
  egR50P0_ok

def egTree52 : Tree := (.skew 1 2 1 (.node 1 egR52P0 (.node 2 (.skew 1 2 1 (.node 1 egR52P1 (.skew 1 2 1 (.node 1 egR52P2 egR52P3)))) egR52P4)))

theorem egTree52_ok : egTree52.okNC 448 1000 3 false (startR 52).1 (startR 52).2.1 (startR 52).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR52P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR52P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR52P2_ok egR52P3_ok)))) egR52P4_ok)))

def egTree54 : Tree := egR54P0

theorem egTree54_ok : egTree54.okNC 448 1000 3 false (startR 54).1 (startR 54).2.1 (startR 54).2.2 = true :=
  egR54P0_ok

def egTree56 : Tree := (.skew 1 2 1 (.node 1 egR56P0 (.node 2 (.skew 1 2 1 (.node 1 egR56P1 (.skew 1 2 1 (.node 1 egR56P2 egR56P3)))) egR56P4)))

theorem egTree56_ok : egTree56.okNC 448 1000 3 false (startR 56).1 (startR 56).2.1 (startR 56).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR56P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR56P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR56P2_ok egR56P3_ok)))) egR56P4_ok)))

def egTree58 : Tree := egR58P0

theorem egTree58_ok : egTree58.okNC 448 1000 3 false (startR 58).1 (startR 58).2.1 (startR 58).2.2 = true :=
  egR58P0_ok

def egTree60 : Tree := (.skew 1 2 1 (.node 1 egR60P0 (.node 2 (.skew 1 2 1 (.node 1 egR60P1 (.skew 1 2 1 (.node 1 egR60P2 (.node 1 egR60P3 (.node 2 egR60P4 egR60P5)))))) egR60P6)))

theorem egTree60_ok : egTree60.okNC 448 1000 3 false (startR 60).1 (startR 60).2.1 (startR 60).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR60P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR60P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR60P2_ok (Tree.okNC_node (by decide) egR60P3_ok (Tree.okNC_node (by decide) egR60P4_ok egR60P5_ok)))))) egR60P6_ok)))

def egTree62 : Tree := egR62P0

theorem egTree62_ok : egTree62.okNC 448 1000 3 false (startR 62).1 (startR 62).2.1 (startR 62).2.2 = true :=
  egR62P0_ok

def egTree66 : Tree := egR66P0

theorem egTree66_ok : egTree66.okNC 448 1000 3 false (startR 66).1 (startR 66).2.1 (startR 66).2.2 = true :=
  egR66P0_ok

def egTree68 : Tree := (.skew 1 2 1 (.node 1 egR68P0 (.node 2 (.skew 1 2 1 (.node 1 egR68P1 (.skew 1 2 1 (.node 1 egR68P2 egR68P3)))) egR68P4)))

theorem egTree68_ok : egTree68.okNC 448 1000 3 false (startR 68).1 (startR 68).2.1 (startR 68).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR68P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR68P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR68P2_ok egR68P3_ok)))) egR68P4_ok)))

def egTree70 : Tree := egR70P0

theorem egTree70_ok : egTree70.okNC 448 1000 3 false (startR 70).1 (startR 70).2.1 (startR 70).2.2 = true :=
  egR70P0_ok

def egTree72 : Tree := (.skew 1 2 1 (.node 1 egR72P0 (.node 2 (.skew 1 2 1 (.node 1 egR72P1 (.skew 1 2 1 (.node 1 egR72P2 (.skew 1 2 1 (.node 1 egR72P3 egR72P4)))))) egR72P5)))

theorem egTree72_ok : egTree72.okNC 448 1000 3 false (startR 72).1 (startR 72).2.1 (startR 72).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR72P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR72P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR72P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR72P3_ok egR72P4_ok)))))) egR72P5_ok)))

def egTree74 : Tree := egR74P0

theorem egTree74_ok : egTree74.okNC 448 1000 3 false (startR 74).1 (startR 74).2.1 (startR 74).2.2 = true :=
  egR74P0_ok

def egTree76 : Tree := (.skew 1 2 1 (.node 1 egR76P0 (.node 2 (.skew 1 2 1 (.node 1 egR76P1 (.skew 1 2 1 (.node 1 egR76P2 (.node 1 egR76P3 (.node 2 egR76P4 egR76P5)))))) egR76P6)))

theorem egTree76_ok : egTree76.okNC 448 1000 3 false (startR 76).1 (startR 76).2.1 (startR 76).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR76P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR76P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR76P2_ok (Tree.okNC_node (by decide) egR76P3_ok (Tree.okNC_node (by decide) egR76P4_ok egR76P5_ok)))))) egR76P6_ok)))

def egTree78 : Tree := egR78P0

theorem egTree78_ok : egTree78.okNC 448 1000 3 false (startR 78).1 (startR 78).2.1 (startR 78).2.2 = true :=
  egR78P0_ok

def egTree80 : Tree := (.skew 1 2 1 (.node 1 egR80P0 (.node 2 (.skew 1 2 1 (.node 1 egR80P1 (.skew 1 2 1 (.node 1 egR80P2 (.skew 1 2 1 (.node 1 egR80P3 (.skew 1 2 1 (.node 1 egR80P4 egR80P5)))))))) egR80P6)))

theorem egTree80_ok : egTree80.okNC 448 1000 3 false (startR 80).1 (startR 80).2.1 (startR 80).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR80P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR80P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR80P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR80P3_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR80P4_ok egR80P5_ok)))))))) egR80P6_ok)))

def egTree82 : Tree := egR82P0

theorem egTree82_ok : egTree82.okNC 448 1000 3 false (startR 82).1 (startR 82).2.1 (startR 82).2.2 = true :=
  egR82P0_ok

def egTree84 : Tree := (.skew 1 2 1 (.node 1 egR84P0 (.node 2 (.skew 1 2 1 (.node 1 egR84P1 (.skew 1 2 1 (.node 1 egR84P2 egR84P3)))) egR84P4)))

theorem egTree84_ok : egTree84.okNC 448 1000 3 false (startR 84).1 (startR 84).2.1 (startR 84).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR84P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR84P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR84P2_ok egR84P3_ok)))) egR84P4_ok)))

def egTree86 : Tree := egR86P0

theorem egTree86_ok : egTree86.okNC 448 1000 3 false (startR 86).1 (startR 86).2.1 (startR 86).2.2 = true :=
  egR86P0_ok

def egTree88 : Tree := (.skew 1 2 1 (.node 1 egR88P0 (.node 2 (.skew 1 2 1 (.node 1 egR88P1 (.skew 1 2 1 (.node 1 egR88P2 (.skew 1 2 1 (.node 1 egR88P3 egR88P4)))))) egR88P5)))

theorem egTree88_ok : egTree88.okNC 448 1000 3 false (startR 88).1 (startR 88).2.1 (startR 88).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR88P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR88P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR88P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR88P3_ok egR88P4_ok)))))) egR88P5_ok)))

def egTree90 : Tree := egR90P0

theorem egTree90_ok : egTree90.okNC 448 1000 3 false (startR 90).1 (startR 90).2.1 (startR 90).2.2 = true :=
  egR90P0_ok

def egTree92 : Tree := (.skew 1 2 1 (.node 1 egR92P0 (.node 2 (.skew 1 2 1 (.node 1 egR92P1 (.skew 1 2 1 (.node 1 egR92P2 (.node 1 egR92P3 (.node 2 egR92P4 egR92P5)))))) egR92P6)))

theorem egTree92_ok : egTree92.okNC 448 1000 3 false (startR 92).1 (startR 92).2.1 (startR 92).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR92P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR92P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR92P2_ok (Tree.okNC_node (by decide) egR92P3_ok (Tree.okNC_node (by decide) egR92P4_ok egR92P5_ok)))))) egR92P6_ok)))

def egTree94 : Tree := egR94P0

theorem egTree94_ok : egTree94.okNC 448 1000 3 false (startR 94).1 (startR 94).2.1 (startR 94).2.2 = true :=
  egR94P0_ok

def egTree96 : Tree := (.skew 1 2 1 (.node 1 egR96P0 (.node 2 (.skew 1 2 1 (.node 1 egR96P1 (.skew 1 2 1 (.node 1 egR96P2 (.skew 1 2 1 (.node 1 egR96P3 (.skew 1 2 1 (.node 1 (.node 1 (.node 1 egR96P4 (.node 1 egR96P5 egR96P6)) egR96P7) egR96P8)))))))) egR96P9)))

theorem egTree96_ok : egTree96.okNC 448 1000 3 false (startR 96).1 (startR 96).2.1 (startR 96).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR96P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR96P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR96P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR96P3_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) egR96P4_ok (Tree.okNC_node (by decide) egR96P5_ok egR96P6_ok)) egR96P7_ok) egR96P8_ok)))))))) egR96P9_ok)))

def egTree98 : Tree := egR98P0

theorem egTree98_ok : egTree98.okNC 448 1000 3 false (startR 98).1 (startR 98).2.1 (startR 98).2.2 = true :=
  egR98P0_ok

def egTree100 : Tree := (.skew 1 2 1 (.node 1 egR100P0 (.node 2 (.skew 1 2 1 (.node 1 egR100P1 (.skew 1 2 1 (.node 1 egR100P2 egR100P3)))) egR100P4)))

theorem egTree100_ok : egTree100.okNC 448 1000 3 false (startR 100).1 (startR 100).2.1 (startR 100).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR100P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR100P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR100P2_ok egR100P3_ok)))) egR100P4_ok)))

def egTree102 : Tree := egR102P0

theorem egTree102_ok : egTree102.okNC 448 1000 3 false (startR 102).1 (startR 102).2.1 (startR 102).2.2 = true :=
  egR102P0_ok

def egTree104 : Tree := (.skew 1 2 1 (.node 1 egR104P0 (.node 2 (.skew 1 2 1 (.node 1 egR104P1 (.skew 1 2 1 (.node 1 egR104P2 (.skew 1 2 1 (.node 1 egR104P3 egR104P4)))))) egR104P5)))

theorem egTree104_ok : egTree104.okNC 448 1000 3 false (startR 104).1 (startR 104).2.1 (startR 104).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR104P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR104P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR104P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR104P3_ok egR104P4_ok)))))) egR104P5_ok)))

def egTree106 : Tree := egR106P0

theorem egTree106_ok : egTree106.okNC 448 1000 3 false (startR 106).1 (startR 106).2.1 (startR 106).2.2 = true :=
  egR106P0_ok

def egTree108 : Tree := (.skew 1 2 1 (.node 1 egR108P0 (.node 2 (.skew 1 2 1 (.node 1 egR108P1 (.skew 1 2 1 (.node 1 egR108P2 (.node 1 egR108P3 (.node 2 egR108P4 egR108P5)))))) egR108P6)))

theorem egTree108_ok : egTree108.okNC 448 1000 3 false (startR 108).1 (startR 108).2.1 (startR 108).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR108P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR108P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR108P2_ok (Tree.okNC_node (by decide) egR108P3_ok (Tree.okNC_node (by decide) egR108P4_ok egR108P5_ok)))))) egR108P6_ok)))

def egTree110 : Tree := egR110P0

theorem egTree110_ok : egTree110.okNC 448 1000 3 false (startR 110).1 (startR 110).2.1 (startR 110).2.2 = true :=
  egR110P0_ok

def egTree112 : Tree := (.skew 1 2 1 (.node 1 egR112P0 (.node 2 (.skew 1 2 1 (.node 1 egR112P1 (.skew 1 2 1 (.node 1 egR112P2 (.skew 1 2 1 (.node 1 egR112P3 (.skew 1 2 1 (.node 1 (.node 1 egR112P4 egR112P5) egR112P6)))))))) egR112P7)))

theorem egTree112_ok : egTree112.okNC 448 1000 3 false (startR 112).1 (startR 112).2.1 (startR 112).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR112P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR112P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR112P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR112P3_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) egR112P4_ok egR112P5_ok) egR112P6_ok)))))))) egR112P7_ok)))

def egTree114 : Tree := egR114P0

theorem egTree114_ok : egTree114.okNC 448 1000 3 false (startR 114).1 (startR 114).2.1 (startR 114).2.2 = true :=
  egR114P0_ok

def egTree116 : Tree := (.skew 1 2 1 (.node 1 egR116P0 (.node 2 (.skew 1 2 1 (.node 1 egR116P1 (.skew 1 2 1 (.node 1 egR116P2 egR116P3)))) egR116P4)))

theorem egTree116_ok : egTree116.okNC 448 1000 3 false (startR 116).1 (startR 116).2.1 (startR 116).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR116P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR116P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR116P2_ok egR116P3_ok)))) egR116P4_ok)))

def egTree118 : Tree := egR118P0

theorem egTree118_ok : egTree118.okNC 448 1000 3 false (startR 118).1 (startR 118).2.1 (startR 118).2.2 = true :=
  egR118P0_ok

def egTree120 : Tree := (.skew 1 2 1 (.node 1 egR120P0 (.node 2 (.skew 1 2 1 (.node 1 egR120P1 (.skew 1 2 1 (.node 1 egR120P2 egR120P3)))) egR120P4)))

theorem egTree120_ok : egTree120.okNC 448 1000 3 false (startR 120).1 (startR 120).2.1 (startR 120).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR120P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR120P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR120P2_ok egR120P3_ok)))) egR120P4_ok)))

def egTree122 : Tree := egR122P0

theorem egTree122_ok : egTree122.okNC 448 1000 3 false (startR 122).1 (startR 122).2.1 (startR 122).2.2 = true :=
  egR122P0_ok

def egTree124 : Tree := (.skew 1 2 1 (.node 1 egR124P0 (.node 2 (.skew 1 2 1 (.node 1 egR124P1 (.skew 1 2 1 (.node 1 egR124P2 (.node 1 egR124P3 (.node 2 egR124P4 egR124P5)))))) egR124P6)))

theorem egTree124_ok : egTree124.okNC 448 1000 3 false (startR 124).1 (startR 124).2.1 (startR 124).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR124P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR124P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR124P2_ok (Tree.okNC_node (by decide) egR124P3_ok (Tree.okNC_node (by decide) egR124P4_ok egR124P5_ok)))))) egR124P6_ok)))

def egTree126 : Tree := egR126P0

theorem egTree126_ok : egTree126.okNC 448 1000 3 false (startR 126).1 (startR 126).2.1 (startR 126).2.2 = true :=
  egR126P0_ok

def egTree128 : Tree := (.skew 1 2 1 (.node 1 egR128P0 (.node 2 (.skew 1 2 1 (.node 1 egR128P1 (.skew 1 2 1 (.node 1 egR128P2 (.skew 1 2 1 (.node 1 egR128P3 (.skew 1 2 1 (.node 1 (.node 1 egR128P4 egR128P5) egR128P6)))))))) egR128P7)))

theorem egTree128_ok : egTree128.okNC 448 1000 3 false (startR 128).1 (startR 128).2.1 (startR 128).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR128P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR128P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR128P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR128P3_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) egR128P4_ok egR128P5_ok) egR128P6_ok)))))))) egR128P7_ok)))

def egTree130 : Tree := egR130P0

theorem egTree130_ok : egTree130.okNC 448 1000 3 false (startR 130).1 (startR 130).2.1 (startR 130).2.2 = true :=
  egR130P0_ok

def egTree132 : Tree := (.skew 1 2 1 (.node 1 egR132P0 (.node 2 (.skew 1 2 1 (.node 1 egR132P1 (.skew 1 2 1 (.node 1 egR132P2 egR132P3)))) egR132P4)))

theorem egTree132_ok : egTree132.okNC 448 1000 3 false (startR 132).1 (startR 132).2.1 (startR 132).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR132P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR132P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR132P2_ok egR132P3_ok)))) egR132P4_ok)))

def egTree134 : Tree := egR134P0

theorem egTree134_ok : egTree134.okNC 448 1000 3 false (startR 134).1 (startR 134).2.1 (startR 134).2.2 = true :=
  egR134P0_ok

def egTree136 : Tree := (.skew 1 2 1 (.node 1 egR136P0 (.node 2 (.skew 1 2 1 (.node 1 egR136P1 (.skew 1 2 1 (.node 1 egR136P2 (.skew 1 2 1 (.node 1 egR136P3 egR136P4)))))) egR136P5)))

theorem egTree136_ok : egTree136.okNC 448 1000 3 false (startR 136).1 (startR 136).2.1 (startR 136).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR136P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR136P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR136P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR136P3_ok egR136P4_ok)))))) egR136P5_ok)))

def egTree138 : Tree := egR138P0

theorem egTree138_ok : egTree138.okNC 448 1000 3 false (startR 138).1 (startR 138).2.1 (startR 138).2.2 = true :=
  egR138P0_ok

def egTree140 : Tree := (.skew 1 2 1 (.node 1 egR140P0 (.node 2 (.skew 1 2 1 (.node 1 egR140P1 (.skew 1 2 1 (.node 1 egR140P2 (.node 1 egR140P3 (.node 2 egR140P4 egR140P5)))))) egR140P6)))

theorem egTree140_ok : egTree140.okNC 448 1000 3 false (startR 140).1 (startR 140).2.1 (startR 140).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR140P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR140P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR140P2_ok (Tree.okNC_node (by decide) egR140P3_ok (Tree.okNC_node (by decide) egR140P4_ok egR140P5_ok)))))) egR140P6_ok)))

def egTree142 : Tree := egR142P0

theorem egTree142_ok : egTree142.okNC 448 1000 3 false (startR 142).1 (startR 142).2.1 (startR 142).2.2 = true :=
  egR142P0_ok

def egTree144 : Tree := (.skew 1 2 1 (.node 1 egR144P0 (.node 2 (.skew 1 2 1 (.node 1 egR144P1 (.skew 1 2 1 (.node 1 egR144P2 (.skew 1 2 1 (.node 1 egR144P3 (.skew 1 2 1 (.node 1 egR144P4 egR144P5)))))))) egR144P6)))

theorem egTree144_ok : egTree144.okNC 448 1000 3 false (startR 144).1 (startR 144).2.1 (startR 144).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR144P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR144P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR144P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR144P3_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR144P4_ok egR144P5_ok)))))))) egR144P6_ok)))

def egTree146 : Tree := egR146P0

theorem egTree146_ok : egTree146.okNC 448 1000 3 false (startR 146).1 (startR 146).2.1 (startR 146).2.2 = true :=
  egR146P0_ok

def egTree148 : Tree := (.skew 1 2 1 (.node 1 egR148P0 (.node 2 (.skew 1 2 1 (.node 1 egR148P1 (.skew 1 2 1 (.node 1 egR148P2 egR148P3)))) egR148P4)))

theorem egTree148_ok : egTree148.okNC 448 1000 3 false (startR 148).1 (startR 148).2.1 (startR 148).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR148P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR148P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR148P2_ok egR148P3_ok)))) egR148P4_ok)))

def egTree150 : Tree := egR150P0

theorem egTree150_ok : egTree150.okNC 448 1000 3 false (startR 150).1 (startR 150).2.1 (startR 150).2.2 = true :=
  egR150P0_ok

def egTree152 : Tree := (.skew 1 2 1 (.node 1 egR152P0 (.node 2 (.skew 1 2 1 (.node 1 egR152P1 (.skew 1 2 1 (.node 1 egR152P2 (.skew 1 2 1 (.node 1 egR152P3 egR152P4)))))) egR152P5)))

theorem egTree152_ok : egTree152.okNC 448 1000 3 false (startR 152).1 (startR 152).2.1 (startR 152).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR152P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR152P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR152P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR152P3_ok egR152P4_ok)))))) egR152P5_ok)))

def egTree154 : Tree := egR154P0

theorem egTree154_ok : egTree154.okNC 448 1000 3 false (startR 154).1 (startR 154).2.1 (startR 154).2.2 = true :=
  egR154P0_ok

def egTree156 : Tree := (.skew 1 2 1 (.node 1 egR156P0 (.node 2 (.skew 1 2 1 (.node 1 egR156P1 (.skew 1 2 1 (.node 1 egR156P2 (.node 1 egR156P3 (.node 2 egR156P4 egR156P5)))))) egR156P6)))

theorem egTree156_ok : egTree156.okNC 448 1000 3 false (startR 156).1 (startR 156).2.1 (startR 156).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR156P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR156P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR156P2_ok (Tree.okNC_node (by decide) egR156P3_ok (Tree.okNC_node (by decide) egR156P4_ok egR156P5_ok)))))) egR156P6_ok)))

def egTree158 : Tree := egR158P0

theorem egTree158_ok : egTree158.okNC 448 1000 3 false (startR 158).1 (startR 158).2.1 (startR 158).2.2 = true :=
  egR158P0_ok

def egTree160 : Tree := (.skew 1 2 1 (.node 1 egR160P0 (.node 2 (.skew 1 2 1 (.node 1 egR160P1 (.skew 1 2 1 (.node 1 egR160P2 (.skew 1 2 1 (.node 1 egR160P3 (.skew 1 2 1 (.node 1 (.node 1 (.node 1 egR160P4 (.node 1 (.node 2 egR160P5 egR160P6) egR160P7)) egR160P8) egR160P9)))))))) egR160P10)))

theorem egTree160_ok : egTree160.okNC 448 1000 3 false (startR 160).1 (startR 160).2.1 (startR 160).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR160P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR160P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR160P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR160P3_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) egR160P4_ok (Tree.okNC_node (by decide) (Tree.okNC_node (by decide) egR160P5_ok egR160P6_ok) egR160P7_ok)) egR160P8_ok) egR160P9_ok)))))))) egR160P10_ok)))

def egTree162 : Tree := egR162P0

theorem egTree162_ok : egTree162.okNC 448 1000 3 false (startR 162).1 (startR 162).2.1 (startR 162).2.2 = true :=
  egR162P0_ok

def egTree164 : Tree := (.skew 1 2 1 (.node 1 egR164P0 (.node 2 (.skew 1 2 1 (.node 1 egR164P1 (.skew 1 2 1 (.node 1 egR164P2 egR164P3)))) egR164P4)))

theorem egTree164_ok : egTree164.okNC 448 1000 3 false (startR 164).1 (startR 164).2.1 (startR 164).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR164P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR164P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR164P2_ok egR164P3_ok)))) egR164P4_ok)))

def egTree166 : Tree := egR166P0

theorem egTree166_ok : egTree166.okNC 448 1000 3 false (startR 166).1 (startR 166).2.1 (startR 166).2.2 = true :=
  egR166P0_ok

def egTree168 : Tree := (.skew 1 2 1 (.node 1 egR168P0 (.node 2 (.skew 1 2 1 (.node 1 egR168P1 (.skew 1 2 1 (.node 1 egR168P2 (.skew 1 2 1 (.node 1 egR168P3 egR168P4)))))) egR168P5)))

theorem egTree168_ok : egTree168.okNC 448 1000 3 false (startR 168).1 (startR 168).2.1 (startR 168).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR168P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR168P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR168P2_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR168P3_ok egR168P4_ok)))))) egR168P5_ok)))

def egTree170 : Tree := egR170P0

theorem egTree170_ok : egTree170.okNC 448 1000 3 false (startR 170).1 (startR 170).2.1 (startR 170).2.2 = true :=
  egR170P0_ok

def egTree172 : Tree := (.skew 1 2 1 (.node 1 egR172P0 (.node 2 (.skew 1 2 1 (.node 1 egR172P1 (.skew 1 2 1 (.node 1 egR172P2 (.node 1 egR172P3 (.node 2 egR172P4 egR172P5)))))) egR172P6)))

theorem egTree172_ok : egTree172.okNC 448 1000 3 false (startR 172).1 (startR 172).2.1 (startR 172).2.2 = true :=
  (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR172P0_ok (Tree.okNC_node (by decide) (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR172P1_ok (Tree.okNC_skew (by decide) (by decide) (by decide) (Tree.okNC_node (by decide) egR172P2_ok (Tree.okNC_node (by decide) egR172P3_ok (Tree.okNC_node (by decide) egR172P4_ok egR172P5_ok)))))) egR172P6_ok)))

def egTree174 : Tree := egR174P0

theorem egTree174_ok : egTree174.okNC 448 1000 3 false (startR 174).1 (startR 174).2.1 (startR 174).2.2 = true :=
  egR174P0_ok

/-- The trees for the even R < 178 outside the closing set. -/
def smallTrees : List (Nat × Tree) := [(6, egTree6), (10, egTree10), (12, egTree12), (14, egTree14), (18, egTree18), (20, egTree20), (22, egTree22), (26, egTree26), (28, egTree28), (30, egTree30), (34, egTree34), (36, egTree36), (38, egTree38), (40, egTree40), (42, egTree42), (44, egTree44), (46, egTree46), (50, egTree50), (52, egTree52), (54, egTree54), (56, egTree56), (58, egTree58), (60, egTree60), (62, egTree62), (66, egTree66), (68, egTree68), (70, egTree70), (72, egTree72), (74, egTree74), (76, egTree76), (78, egTree78), (80, egTree80), (82, egTree82), (84, egTree84), (86, egTree86), (88, egTree88), (90, egTree90), (92, egTree92), (94, egTree94), (96, egTree96), (98, egTree98), (100, egTree100), (102, egTree102), (104, egTree104), (106, egTree106), (108, egTree108), (110, egTree110), (112, egTree112), (114, egTree114), (116, egTree116), (118, egTree118), (120, egTree120), (122, egTree122), (124, egTree124), (126, egTree126), (128, egTree128), (130, egTree130), (132, egTree132), (134, egTree134), (136, egTree136), (138, egTree138), (140, egTree140), (142, egTree142), (144, egTree144), (146, egTree146), (148, egTree148), (150, egTree150), (152, egTree152), (154, egTree154), (156, egTree156), (158, egTree158), (160, egTree160), (162, egTree162), (164, egTree164), (166, egTree166), (168, egTree168), (170, egTree170), (172, egTree172), (174, egTree174)]

theorem small_trees_ok :
    ∀ p ∈ smallTrees, p.2.okNC 448 1000 3 false (startR p.1).1 (startR p.1).2.1 (startR p.1).2.2 = true :=
  List.forall_mem_cons.2 ⟨egTree6_ok, List.forall_mem_cons.2 ⟨egTree10_ok, List.forall_mem_cons.2 ⟨egTree12_ok, List.forall_mem_cons.2 ⟨egTree14_ok, List.forall_mem_cons.2 ⟨egTree18_ok, List.forall_mem_cons.2 ⟨egTree20_ok, List.forall_mem_cons.2 ⟨egTree22_ok, List.forall_mem_cons.2 ⟨egTree26_ok, List.forall_mem_cons.2 ⟨egTree28_ok, List.forall_mem_cons.2 ⟨egTree30_ok, List.forall_mem_cons.2 ⟨egTree34_ok, List.forall_mem_cons.2 ⟨egTree36_ok, List.forall_mem_cons.2 ⟨egTree38_ok, List.forall_mem_cons.2 ⟨egTree40_ok, List.forall_mem_cons.2 ⟨egTree42_ok, List.forall_mem_cons.2 ⟨egTree44_ok, List.forall_mem_cons.2 ⟨egTree46_ok, List.forall_mem_cons.2 ⟨egTree50_ok, List.forall_mem_cons.2 ⟨egTree52_ok, List.forall_mem_cons.2 ⟨egTree54_ok, List.forall_mem_cons.2 ⟨egTree56_ok, List.forall_mem_cons.2 ⟨egTree58_ok, List.forall_mem_cons.2 ⟨egTree60_ok, List.forall_mem_cons.2 ⟨egTree62_ok, List.forall_mem_cons.2 ⟨egTree66_ok, List.forall_mem_cons.2 ⟨egTree68_ok, List.forall_mem_cons.2 ⟨egTree70_ok, List.forall_mem_cons.2 ⟨egTree72_ok, List.forall_mem_cons.2 ⟨egTree74_ok, List.forall_mem_cons.2 ⟨egTree76_ok, List.forall_mem_cons.2 ⟨egTree78_ok, List.forall_mem_cons.2 ⟨egTree80_ok, List.forall_mem_cons.2 ⟨egTree82_ok, List.forall_mem_cons.2 ⟨egTree84_ok, List.forall_mem_cons.2 ⟨egTree86_ok, List.forall_mem_cons.2 ⟨egTree88_ok, List.forall_mem_cons.2 ⟨egTree90_ok, List.forall_mem_cons.2 ⟨egTree92_ok, List.forall_mem_cons.2 ⟨egTree94_ok, List.forall_mem_cons.2 ⟨egTree96_ok, List.forall_mem_cons.2 ⟨egTree98_ok, List.forall_mem_cons.2 ⟨egTree100_ok, List.forall_mem_cons.2 ⟨egTree102_ok, List.forall_mem_cons.2 ⟨egTree104_ok, List.forall_mem_cons.2 ⟨egTree106_ok, List.forall_mem_cons.2 ⟨egTree108_ok, List.forall_mem_cons.2 ⟨egTree110_ok, List.forall_mem_cons.2 ⟨egTree112_ok, List.forall_mem_cons.2 ⟨egTree114_ok, List.forall_mem_cons.2 ⟨egTree116_ok, List.forall_mem_cons.2 ⟨egTree118_ok, List.forall_mem_cons.2 ⟨egTree120_ok, List.forall_mem_cons.2 ⟨egTree122_ok, List.forall_mem_cons.2 ⟨egTree124_ok, List.forall_mem_cons.2 ⟨egTree126_ok, List.forall_mem_cons.2 ⟨egTree128_ok, List.forall_mem_cons.2 ⟨egTree130_ok, List.forall_mem_cons.2 ⟨egTree132_ok, List.forall_mem_cons.2 ⟨egTree134_ok, List.forall_mem_cons.2 ⟨egTree136_ok, List.forall_mem_cons.2 ⟨egTree138_ok, List.forall_mem_cons.2 ⟨egTree140_ok, List.forall_mem_cons.2 ⟨egTree142_ok, List.forall_mem_cons.2 ⟨egTree144_ok, List.forall_mem_cons.2 ⟨egTree146_ok, List.forall_mem_cons.2 ⟨egTree148_ok, List.forall_mem_cons.2 ⟨egTree150_ok, List.forall_mem_cons.2 ⟨egTree152_ok, List.forall_mem_cons.2 ⟨egTree154_ok, List.forall_mem_cons.2 ⟨egTree156_ok, List.forall_mem_cons.2 ⟨egTree158_ok, List.forall_mem_cons.2 ⟨egTree160_ok, List.forall_mem_cons.2 ⟨egTree162_ok, List.forall_mem_cons.2 ⟨egTree164_ok, List.forall_mem_cons.2 ⟨egTree166_ok, List.forall_mem_cons.2 ⟨egTree168_ok, List.forall_mem_cons.2 ⟨egTree170_ok, List.forall_mem_cons.2 ⟨egTree172_ok, List.forall_mem_cons.2 ⟨egTree174_ok, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem small_trees_cover :
    ((List.range 88).all fun r => closingSet.contains (2 * (r + 1)) ||
      smallTrees.any fun (p : Nat × Tree) => p.1 == 2 * (r + 1)) = true := by
  decide +kernel

/-- **The endgame, for the machine.**  For every even R ≥ 2 outside the closing set {2, 4, 8, 16, 24, 32, 48, 64,
176}, and every phase-0 pass start — walls at a, b and c = E − R − 1, width E, with a odd, b even, E even and every gap
at least 448 — the machine runs a number of rounds (up to the round at which this start's pass completes, its
end-meeting chain breaks, or it leaves phase 0, per the tree) without halting, reaching a round start (the one
`roundsZ` computes: the mark model covers these rounds), and every end meeting on the way is at distance at least 3:
the run does not close. -/
theorem endgame_no_close (R : Nat) (hR : R % 2 = 0) (hR2 : 2 ≤ R) (hS : closingSet.contains R = false)
    (a b E : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) (hE : E % 2 = 0)
    (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) :
    ∃ n kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = some (roundStart ms' W') ∧
      roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
      ∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d := by
  by_cases hR178 : 178 ≤ R
  · -- the tree for every R ≥ 178, at the point (a, b, E, R)
    let y : List Int := [((a : Int) - 1) / 2, (b : Int) / 2, (E : Int) / 2, (R : Int) / 2]
    have hy : inCone symStart.2.2 448 y := by
      intro f hf
      simp only [symStart, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl | rfl | rfl <;>
        simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
    have hs : agL y symStart.1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] := by
      refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
        simp only [agN, y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;>
        omega
    have hW : agN y symStart.2.1 E := by simp only [agN, y, symStart, YForm.eval, dot]; omega
    exact Tree.soundNC 448 1000 4 symTree false _ _ _ sym_tree_ok y rfl hy _ _ hs hW (fun h => by cases h)
  · -- the tree for R
    have hcov := small_trees_cover
    rw [List.all_eq_true] at hcov
    have hr := hcov (R / 2 - 1) (by simp only [List.mem_range]; omega)
    have e : 2 * (R / 2 - 1 + 1) = R := by omega
    rw [e, hS, Bool.false_or, List.any_eq_true] at hr
    obtain ⟨⟨R', t⟩, hmem, hR'⟩ := hr
    simp only [beq_iff_eq] at hR'
    subst hR'
    have ht := small_trees_ok _ hmem
    simp only at ht
    let y : List Int := [((a : Int) - 1) / 2, (b : Int) / 2, (E : Int) / 2]
    have hy : inCone (startR R').2.2 448 y := by
      intro f hf
      simp only [startR, List.mem_cons, List.mem_nil_iff, or_false] at hf
      rcases hf with rfl | rfl | rfl <;>
        simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot] <;> omega
    have hs : agL y (startR R').1 [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R' - 1⟩] := by
      refine ⟨⟨rfl, ?_⟩, ⟨rfl, ?_⟩, ⟨rfl, ?_⟩, trivial⟩ <;>
        simp only [agN, y, YForm.eval, YForm.addc, dot] <;> omega
    have hW : agN y (startR R').2.1 E := by simp only [agN, y, startR, YForm.eval, dot]; omega
    exact Tree.soundNC 448 1000 3 t false _ _ _ ht y rfl hy _ _ hs hW (fun h => by cases h)
