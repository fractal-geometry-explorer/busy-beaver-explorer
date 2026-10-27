import EndgamePieces0
import EndgamePieces1
import EndgamePieces2
import EndgamePieces3
open BB6 BB6.Sym

/-! # The endgame as a theorem

The phase-0 pass starts with R ≥ 178 form one class, with R a coordinate (`symStart`); for each even R < 178, the pass
starts with that R form a class (`startR R`).  A tree of coordinate splits and skews for each class (built by the
untrusted program `ExploreNC.lean`, so it covers the class by construction; `adv` nodes run the rounds before a split
once for the whole subtree) is checked by the proved function `Tree.okEnd`, evaluated by the kernel (`decide +kernel`;
no compiler is trusted): every leaf's run is close-free and ends at an end event (`BB6/Ends.lean`), or, for R in the
closing set, the leaf shows L₁ in R's class.  The checks are cut into subtrees with a theorem each, in the modules
`EndgamePieces0`, … (compiled in parallel), and assembled here by `Tree.okEnd_node` and `Tree.okEnd_skew`.
`endgame_stretch` is the statement for the machine. -/

/-- The tree for every R ≥ 178. -/
def symTree : Tree := (.node 3 (.skew 1 2 1 (.node 1 egSymP0 (.node 2 (.skew 1 2 1 (.node 1 egSymP1 (.node 3 (.skew 1 2 1 (.node 1 egSymP2 (.skew 1 2 1 (.node 1 egSymP3 (.node 3 (.skew 1 2 1 (.node 1 (.node 3 (.node 1 (.node 3 egSymP4 (.node 1 (.node 3 (.skew 1 3 1 (.node 1 egSymP5 egSymP6)) egSymP7) (.node 1 (.skew 2 3 1 (.node 2 (.node 3 egSymP8 egSymP9) egSymP10)) egSymP11))) egSymP12) (.node 1 (.node 3 (.skew 1 2 1 (.node 1 egSymP13 egSymP14)) (.skew 1 2 1 (.node 1 egSymP15 (.node 3 egSymP16 egSymP17)))) egSymP18)) egSymP19)) (.skew 1 2 1 (.node 1 egSymP20 (.node 3 (.skew 1 2 1 (.node 1 egSymP21 egSymP22)) (.skew 1 2 1 (.node 1 egSymP23 egSymP24)))))))))) (.skew 1 2 1 (.node 1 (.node 3 egSymP25 egSymP26) (.node 1 egSymP27 (.skew 2 3 1 (.node 2 (.node 3 egSymP28 egSymP29) egSymP30)))))))) egSymP31))) egSymP32)

theorem sym_tree_ok : symTree.okEnd 448 1000 4 none EndSpec.endgame false symStartE.1.1 symStartE.1.2.1
    symStartE.1.2.2 symStartE.2 0 none = true :=
  (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP1_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP3_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egSymP4_ok (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP5_ok egSymP6_ok)) egSymP7_ok) (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egSymP8_ok egSymP9_ok) egSymP10_ok)) egSymP11_ok))) egSymP12_ok) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP13_ok egSymP14_ok)) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP15_ok (Tree.okEnd_node (by decide) egSymP16_ok egSymP17_ok)))) egSymP18_ok)) egSymP19_ok)) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP20_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP21_ok egSymP22_ok)) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egSymP23_ok egSymP24_ok)))))))))) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egSymP25_ok egSymP26_ok) (Tree.okEnd_node (by decide) egSymP27_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egSymP28_ok egSymP29_ok) egSymP30_ok)))))))) egSymP31_ok))) egSymP32_ok)

def egTree2 : Tree := egR2P0

theorem egTree2_ok : egTree2.okEnd 448 1000 3 (closeClass 2) EndSpec.endgame false (startE 2).1.1
    (startE 2).1.2.1 (startE 2).1.2.2 (startE 2).2 0 none = true :=
  egR2P0_ok

def egTree4 : Tree := egR4P0

theorem egTree4_ok : egTree4.okEnd 448 1000 3 (closeClass 4) EndSpec.endgame false (startE 4).1.1
    (startE 4).1.2.1 (startE 4).1.2.2 (startE 4).2 0 none = true :=
  egR4P0_ok

def egTree6 : Tree := egR6P0

theorem egTree6_ok : egTree6.okEnd 448 1000 3 (closeClass 6) EndSpec.endgame false (startE 6).1.1
    (startE 6).1.2.1 (startE 6).1.2.2 (startE 6).2 0 none = true :=
  egR6P0_ok

def egTree8 : Tree := egR8P0

theorem egTree8_ok : egTree8.okEnd 448 1000 3 (closeClass 8) EndSpec.endgame false (startE 8).1.1
    (startE 8).1.2.1 (startE 8).1.2.2 (startE 8).2 0 none = true :=
  egR8P0_ok

def egTree10 : Tree := egR10P0

theorem egTree10_ok : egTree10.okEnd 448 1000 3 (closeClass 10) EndSpec.endgame false (startE 10).1.1
    (startE 10).1.2.1 (startE 10).1.2.2 (startE 10).2 0 none = true :=
  egR10P0_ok

def egTree12 : Tree := (.skew 1 2 1 (.node 1 egR12P0 (.node 2 (.skew 1 2 1 (.node 1 egR12P1 (.skew 1 2 1 (.node 1 egR12P2 (.node 1 egR12P3 (.node 2 egR12P4 egR12P5)))))) egR12P6)))

theorem egTree12_ok : egTree12.okEnd 448 1000 3 (closeClass 12) EndSpec.endgame false (startE 12).1.1
    (startE 12).1.2.1 (startE 12).1.2.2 (startE 12).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR12P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR12P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR12P2_ok (Tree.okEnd_node (by decide) egR12P3_ok (Tree.okEnd_node (by decide) egR12P4_ok egR12P5_ok)))))) egR12P6_ok)))

def egTree14 : Tree := egR14P0

theorem egTree14_ok : egTree14.okEnd 448 1000 3 (closeClass 14) EndSpec.endgame false (startE 14).1.1
    (startE 14).1.2.1 (startE 14).1.2.2 (startE 14).2 0 none = true :=
  egR14P0_ok

def egTree16 : Tree := egR16P0

theorem egTree16_ok : egTree16.okEnd 448 1000 3 (closeClass 16) EndSpec.endgame false (startE 16).1.1
    (startE 16).1.2.1 (startE 16).1.2.2 (startE 16).2 0 none = true :=
  egR16P0_ok

def egTree18 : Tree := egR18P0

theorem egTree18_ok : egTree18.okEnd 448 1000 3 (closeClass 18) EndSpec.endgame false (startE 18).1.1
    (startE 18).1.2.1 (startE 18).1.2.2 (startE 18).2 0 none = true :=
  egR18P0_ok

def egTree20 : Tree := (.skew 1 2 1 (.node 1 egR20P0 (.node 2 (.skew 1 2 1 (.node 1 egR20P1 (.skew 1 2 1 (.node 1 egR20P2 egR20P3)))) egR20P4)))

theorem egTree20_ok : egTree20.okEnd 448 1000 3 (closeClass 20) EndSpec.endgame false (startE 20).1.1
    (startE 20).1.2.1 (startE 20).1.2.2 (startE 20).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR20P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR20P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR20P2_ok egR20P3_ok)))) egR20P4_ok)))

def egTree22 : Tree := egR22P0

theorem egTree22_ok : egTree22.okEnd 448 1000 3 (closeClass 22) EndSpec.endgame false (startE 22).1.1
    (startE 22).1.2.1 (startE 22).1.2.2 (startE 22).2 0 none = true :=
  egR22P0_ok

def egTree24 : Tree := (.skew 1 2 1 (.node 1 egR24P0 (.node 2 (.skew 1 2 1 (.node 1 egR24P1 egR24P2)) egR24P3)))

theorem egTree24_ok : egTree24.okEnd 448 1000 3 (closeClass 24) EndSpec.endgame false (startE 24).1.1
    (startE 24).1.2.1 (startE 24).1.2.2 (startE 24).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR24P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR24P1_ok egR24P2_ok)) egR24P3_ok)))

def egTree26 : Tree := egR26P0

theorem egTree26_ok : egTree26.okEnd 448 1000 3 (closeClass 26) EndSpec.endgame false (startE 26).1.1
    (startE 26).1.2.1 (startE 26).1.2.2 (startE 26).2 0 none = true :=
  egR26P0_ok

def egTree28 : Tree := (.skew 1 2 1 (.node 1 egR28P0 (.node 2 (.skew 1 2 1 (.node 1 egR28P1 (.skew 1 2 1 (.node 1 egR28P2 (.node 1 egR28P3 (.node 2 egR28P4 egR28P5)))))) egR28P6)))

theorem egTree28_ok : egTree28.okEnd 448 1000 3 (closeClass 28) EndSpec.endgame false (startE 28).1.1
    (startE 28).1.2.1 (startE 28).1.2.2 (startE 28).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR28P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR28P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR28P2_ok (Tree.okEnd_node (by decide) egR28P3_ok (Tree.okEnd_node (by decide) egR28P4_ok egR28P5_ok)))))) egR28P6_ok)))

def egTree30 : Tree := egR30P0

theorem egTree30_ok : egTree30.okEnd 448 1000 3 (closeClass 30) EndSpec.endgame false (startE 30).1.1
    (startE 30).1.2.1 (startE 30).1.2.2 (startE 30).2 0 none = true :=
  egR30P0_ok

def egTree32 : Tree := (.skew 1 2 1 (.node 1 egR32P0 (.node 2 (.skew 1 2 1 (.node 1 egR32P1 (.skew 1 2 1 (.node 1 egR32P2 (.skew 1 2 1 (.node 1 egR32P3 egR32P4)))))) egR32P5)))

theorem egTree32_ok : egTree32.okEnd 448 1000 3 (closeClass 32) EndSpec.endgame false (startE 32).1.1
    (startE 32).1.2.1 (startE 32).1.2.2 (startE 32).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR32P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR32P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR32P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR32P3_ok egR32P4_ok)))))) egR32P5_ok)))

def egTree34 : Tree := egR34P0

theorem egTree34_ok : egTree34.okEnd 448 1000 3 (closeClass 34) EndSpec.endgame false (startE 34).1.1
    (startE 34).1.2.1 (startE 34).1.2.2 (startE 34).2 0 none = true :=
  egR34P0_ok

def egTree36 : Tree := (.skew 1 2 1 (.node 1 egR36P0 (.node 2 (.skew 1 2 1 (.node 1 egR36P1 (.skew 1 2 1 (.node 1 egR36P2 egR36P3)))) egR36P4)))

theorem egTree36_ok : egTree36.okEnd 448 1000 3 (closeClass 36) EndSpec.endgame false (startE 36).1.1
    (startE 36).1.2.1 (startE 36).1.2.2 (startE 36).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR36P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR36P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR36P2_ok egR36P3_ok)))) egR36P4_ok)))

def egTree38 : Tree := egR38P0

theorem egTree38_ok : egTree38.okEnd 448 1000 3 (closeClass 38) EndSpec.endgame false (startE 38).1.1
    (startE 38).1.2.1 (startE 38).1.2.2 (startE 38).2 0 none = true :=
  egR38P0_ok

def egTree40 : Tree := (.skew 1 2 1 (.node 1 egR40P0 (.node 2 (.skew 1 2 1 (.node 1 egR40P1 (.skew 1 2 1 (.node 1 egR40P2 (.skew 1 2 1 (.node 1 egR40P3 egR40P4)))))) egR40P5)))

theorem egTree40_ok : egTree40.okEnd 448 1000 3 (closeClass 40) EndSpec.endgame false (startE 40).1.1
    (startE 40).1.2.1 (startE 40).1.2.2 (startE 40).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR40P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR40P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR40P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR40P3_ok egR40P4_ok)))))) egR40P5_ok)))

def egTree42 : Tree := egR42P0

theorem egTree42_ok : egTree42.okEnd 448 1000 3 (closeClass 42) EndSpec.endgame false (startE 42).1.1
    (startE 42).1.2.1 (startE 42).1.2.2 (startE 42).2 0 none = true :=
  egR42P0_ok

def egTree44 : Tree := (.skew 1 2 1 (.node 1 egR44P0 (.node 2 (.skew 1 2 1 (.node 1 egR44P1 (.skew 1 2 1 (.node 1 egR44P2 (.node 1 egR44P3 (.node 2 egR44P4 egR44P5)))))) egR44P6)))

theorem egTree44_ok : egTree44.okEnd 448 1000 3 (closeClass 44) EndSpec.endgame false (startE 44).1.1
    (startE 44).1.2.1 (startE 44).1.2.2 (startE 44).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR44P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR44P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR44P2_ok (Tree.okEnd_node (by decide) egR44P3_ok (Tree.okEnd_node (by decide) egR44P4_ok egR44P5_ok)))))) egR44P6_ok)))

def egTree46 : Tree := egR46P0

theorem egTree46_ok : egTree46.okEnd 448 1000 3 (closeClass 46) EndSpec.endgame false (startE 46).1.1
    (startE 46).1.2.1 (startE 46).1.2.2 (startE 46).2 0 none = true :=
  egR46P0_ok

def egTree48 : Tree := (.skew 1 2 1 (.node 1 egR48P0 (.node 2 (.skew 1 2 1 (.node 1 egR48P1 (.skew 1 2 1 (.node 1 egR48P2 (.skew 1 2 1 (.node 1 egR48P3 (.skew 1 2 1 (.node 1 egR48P4 egR48P5)))))))) egR48P6)))

theorem egTree48_ok : egTree48.okEnd 448 1000 3 (closeClass 48) EndSpec.endgame false (startE 48).1.1
    (startE 48).1.2.1 (startE 48).1.2.2 (startE 48).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR48P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR48P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR48P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR48P3_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR48P4_ok egR48P5_ok)))))))) egR48P6_ok)))

def egTree50 : Tree := egR50P0

theorem egTree50_ok : egTree50.okEnd 448 1000 3 (closeClass 50) EndSpec.endgame false (startE 50).1.1
    (startE 50).1.2.1 (startE 50).1.2.2 (startE 50).2 0 none = true :=
  egR50P0_ok

def egTree52 : Tree := (.skew 1 2 1 (.node 1 egR52P0 (.node 2 (.skew 1 2 1 (.node 1 egR52P1 (.skew 1 2 1 (.node 1 egR52P2 egR52P3)))) egR52P4)))

theorem egTree52_ok : egTree52.okEnd 448 1000 3 (closeClass 52) EndSpec.endgame false (startE 52).1.1
    (startE 52).1.2.1 (startE 52).1.2.2 (startE 52).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR52P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR52P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR52P2_ok egR52P3_ok)))) egR52P4_ok)))

def egTree54 : Tree := egR54P0

theorem egTree54_ok : egTree54.okEnd 448 1000 3 (closeClass 54) EndSpec.endgame false (startE 54).1.1
    (startE 54).1.2.1 (startE 54).1.2.2 (startE 54).2 0 none = true :=
  egR54P0_ok

def egTree56 : Tree := (.skew 1 2 1 (.node 1 egR56P0 (.node 2 (.skew 1 2 1 (.node 1 egR56P1 (.skew 1 2 1 (.node 1 egR56P2 egR56P3)))) egR56P4)))

theorem egTree56_ok : egTree56.okEnd 448 1000 3 (closeClass 56) EndSpec.endgame false (startE 56).1.1
    (startE 56).1.2.1 (startE 56).1.2.2 (startE 56).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR56P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR56P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR56P2_ok egR56P3_ok)))) egR56P4_ok)))

def egTree58 : Tree := egR58P0

theorem egTree58_ok : egTree58.okEnd 448 1000 3 (closeClass 58) EndSpec.endgame false (startE 58).1.1
    (startE 58).1.2.1 (startE 58).1.2.2 (startE 58).2 0 none = true :=
  egR58P0_ok

def egTree60 : Tree := (.skew 1 2 1 (.node 1 egR60P0 (.node 2 (.skew 1 2 1 (.node 1 egR60P1 (.skew 1 2 1 (.node 1 egR60P2 (.node 1 egR60P3 (.node 2 egR60P4 egR60P5)))))) egR60P6)))

theorem egTree60_ok : egTree60.okEnd 448 1000 3 (closeClass 60) EndSpec.endgame false (startE 60).1.1
    (startE 60).1.2.1 (startE 60).1.2.2 (startE 60).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR60P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR60P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR60P2_ok (Tree.okEnd_node (by decide) egR60P3_ok (Tree.okEnd_node (by decide) egR60P4_ok egR60P5_ok)))))) egR60P6_ok)))

def egTree62 : Tree := egR62P0

theorem egTree62_ok : egTree62.okEnd 448 1000 3 (closeClass 62) EndSpec.endgame false (startE 62).1.1
    (startE 62).1.2.1 (startE 62).1.2.2 (startE 62).2 0 none = true :=
  egR62P0_ok

def egTree64 : Tree := (.skew 1 2 1 (.node 1 egR64P0 (.node 2 (.skew 1 2 1 (.node 1 egR64P1 (.skew 1 2 1 (.node 1 egR64P2 (.skew 1 2 1 (.node 1 egR64P3 (.skew 1 2 1 (.node 1 egR64P4 egR64P5)))))))) egR64P6)))

theorem egTree64_ok : egTree64.okEnd 448 1000 3 (closeClass 64) EndSpec.endgame false (startE 64).1.1
    (startE 64).1.2.1 (startE 64).1.2.2 (startE 64).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR64P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR64P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR64P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR64P3_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR64P4_ok egR64P5_ok)))))))) egR64P6_ok)))

def egTree66 : Tree := egR66P0

theorem egTree66_ok : egTree66.okEnd 448 1000 3 (closeClass 66) EndSpec.endgame false (startE 66).1.1
    (startE 66).1.2.1 (startE 66).1.2.2 (startE 66).2 0 none = true :=
  egR66P0_ok

def egTree68 : Tree := (.skew 1 2 1 (.node 1 egR68P0 (.node 2 (.skew 1 2 1 (.node 1 egR68P1 (.skew 1 2 1 (.node 1 egR68P2 egR68P3)))) egR68P4)))

theorem egTree68_ok : egTree68.okEnd 448 1000 3 (closeClass 68) EndSpec.endgame false (startE 68).1.1
    (startE 68).1.2.1 (startE 68).1.2.2 (startE 68).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR68P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR68P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR68P2_ok egR68P3_ok)))) egR68P4_ok)))

def egTree70 : Tree := egR70P0

theorem egTree70_ok : egTree70.okEnd 448 1000 3 (closeClass 70) EndSpec.endgame false (startE 70).1.1
    (startE 70).1.2.1 (startE 70).1.2.2 (startE 70).2 0 none = true :=
  egR70P0_ok

def egTree72 : Tree := (.skew 1 2 1 (.node 1 egR72P0 (.node 2 (.skew 1 2 1 (.node 1 egR72P1 (.skew 1 2 1 (.node 1 egR72P2 (.skew 1 2 1 (.node 1 egR72P3 egR72P4)))))) egR72P5)))

theorem egTree72_ok : egTree72.okEnd 448 1000 3 (closeClass 72) EndSpec.endgame false (startE 72).1.1
    (startE 72).1.2.1 (startE 72).1.2.2 (startE 72).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR72P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR72P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR72P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR72P3_ok egR72P4_ok)))))) egR72P5_ok)))

def egTree74 : Tree := egR74P0

theorem egTree74_ok : egTree74.okEnd 448 1000 3 (closeClass 74) EndSpec.endgame false (startE 74).1.1
    (startE 74).1.2.1 (startE 74).1.2.2 (startE 74).2 0 none = true :=
  egR74P0_ok

def egTree76 : Tree := (.skew 1 2 1 (.node 1 egR76P0 (.node 2 (.skew 1 2 1 (.node 1 egR76P1 (.skew 1 2 1 (.node 1 egR76P2 (.node 1 egR76P3 (.node 2 egR76P4 egR76P5)))))) egR76P6)))

theorem egTree76_ok : egTree76.okEnd 448 1000 3 (closeClass 76) EndSpec.endgame false (startE 76).1.1
    (startE 76).1.2.1 (startE 76).1.2.2 (startE 76).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR76P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR76P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR76P2_ok (Tree.okEnd_node (by decide) egR76P3_ok (Tree.okEnd_node (by decide) egR76P4_ok egR76P5_ok)))))) egR76P6_ok)))

def egTree78 : Tree := egR78P0

theorem egTree78_ok : egTree78.okEnd 448 1000 3 (closeClass 78) EndSpec.endgame false (startE 78).1.1
    (startE 78).1.2.1 (startE 78).1.2.2 (startE 78).2 0 none = true :=
  egR78P0_ok

def egTree80 : Tree := (.skew 1 2 1 (.node 1 egR80P0 (.node 2 (.skew 1 2 1 (.node 1 egR80P1 (.skew 1 2 1 (.node 1 egR80P2 (.skew 1 2 1 (.node 1 egR80P3 (.skew 1 2 1 (.node 1 (.node 1 egR80P4 egR80P5) egR80P6)))))))) egR80P7)))

theorem egTree80_ok : egTree80.okEnd 448 1000 3 (closeClass 80) EndSpec.endgame false (startE 80).1.1
    (startE 80).1.2.1 (startE 80).1.2.2 (startE 80).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR80P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR80P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR80P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR80P3_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egR80P4_ok egR80P5_ok) egR80P6_ok)))))))) egR80P7_ok)))

def egTree82 : Tree := egR82P0

theorem egTree82_ok : egTree82.okEnd 448 1000 3 (closeClass 82) EndSpec.endgame false (startE 82).1.1
    (startE 82).1.2.1 (startE 82).1.2.2 (startE 82).2 0 none = true :=
  egR82P0_ok

def egTree84 : Tree := (.skew 1 2 1 (.node 1 egR84P0 (.node 2 (.skew 1 2 1 (.node 1 egR84P1 (.skew 1 2 1 (.node 1 egR84P2 egR84P3)))) egR84P4)))

theorem egTree84_ok : egTree84.okEnd 448 1000 3 (closeClass 84) EndSpec.endgame false (startE 84).1.1
    (startE 84).1.2.1 (startE 84).1.2.2 (startE 84).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR84P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR84P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR84P2_ok egR84P3_ok)))) egR84P4_ok)))

def egTree86 : Tree := egR86P0

theorem egTree86_ok : egTree86.okEnd 448 1000 3 (closeClass 86) EndSpec.endgame false (startE 86).1.1
    (startE 86).1.2.1 (startE 86).1.2.2 (startE 86).2 0 none = true :=
  egR86P0_ok

def egTree88 : Tree := (.skew 1 2 1 (.node 1 egR88P0 (.node 2 (.skew 1 2 1 (.node 1 egR88P1 (.skew 1 2 1 (.node 1 egR88P2 (.skew 1 2 1 (.node 1 egR88P3 egR88P4)))))) egR88P5)))

theorem egTree88_ok : egTree88.okEnd 448 1000 3 (closeClass 88) EndSpec.endgame false (startE 88).1.1
    (startE 88).1.2.1 (startE 88).1.2.2 (startE 88).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR88P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR88P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR88P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR88P3_ok egR88P4_ok)))))) egR88P5_ok)))

def egTree90 : Tree := egR90P0

theorem egTree90_ok : egTree90.okEnd 448 1000 3 (closeClass 90) EndSpec.endgame false (startE 90).1.1
    (startE 90).1.2.1 (startE 90).1.2.2 (startE 90).2 0 none = true :=
  egR90P0_ok

def egTree92 : Tree := (.skew 1 2 1 (.node 1 egR92P0 (.node 2 (.skew 1 2 1 (.node 1 egR92P1 (.skew 1 2 1 (.node 1 egR92P2 (.node 1 egR92P3 (.node 2 egR92P4 egR92P5)))))) egR92P6)))

theorem egTree92_ok : egTree92.okEnd 448 1000 3 (closeClass 92) EndSpec.endgame false (startE 92).1.1
    (startE 92).1.2.1 (startE 92).1.2.2 (startE 92).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR92P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR92P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR92P2_ok (Tree.okEnd_node (by decide) egR92P3_ok (Tree.okEnd_node (by decide) egR92P4_ok egR92P5_ok)))))) egR92P6_ok)))

def egTree94 : Tree := egR94P0

theorem egTree94_ok : egTree94.okEnd 448 1000 3 (closeClass 94) EndSpec.endgame false (startE 94).1.1
    (startE 94).1.2.1 (startE 94).1.2.2 (startE 94).2 0 none = true :=
  egR94P0_ok

def egTree96 : Tree := (.skew 1 2 1 (.node 1 egR96P0 (.node 2 (.skew 1 2 1 (.node 1 egR96P1 (.skew 1 2 1 (.node 1 egR96P2 (.skew 1 2 1 (.node 1 egR96P3 (.skew 1 2 1 (.node 1 (.node 1 (.node 1 egR96P4 (.node 1 egR96P5 egR96P6)) egR96P7) egR96P8)))))))) egR96P9)))

theorem egTree96_ok : egTree96.okEnd 448 1000 3 (closeClass 96) EndSpec.endgame false (startE 96).1.1
    (startE 96).1.2.1 (startE 96).1.2.2 (startE 96).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR96P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR96P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR96P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR96P3_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egR96P4_ok (Tree.okEnd_node (by decide) egR96P5_ok egR96P6_ok)) egR96P7_ok) egR96P8_ok)))))))) egR96P9_ok)))

def egTree98 : Tree := egR98P0

theorem egTree98_ok : egTree98.okEnd 448 1000 3 (closeClass 98) EndSpec.endgame false (startE 98).1.1
    (startE 98).1.2.1 (startE 98).1.2.2 (startE 98).2 0 none = true :=
  egR98P0_ok

def egTree100 : Tree := (.skew 1 2 1 (.node 1 egR100P0 (.node 2 (.skew 1 2 1 (.node 1 egR100P1 (.skew 1 2 1 (.node 1 egR100P2 egR100P3)))) egR100P4)))

theorem egTree100_ok : egTree100.okEnd 448 1000 3 (closeClass 100) EndSpec.endgame false (startE 100).1.1
    (startE 100).1.2.1 (startE 100).1.2.2 (startE 100).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR100P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR100P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR100P2_ok egR100P3_ok)))) egR100P4_ok)))

def egTree102 : Tree := egR102P0

theorem egTree102_ok : egTree102.okEnd 448 1000 3 (closeClass 102) EndSpec.endgame false (startE 102).1.1
    (startE 102).1.2.1 (startE 102).1.2.2 (startE 102).2 0 none = true :=
  egR102P0_ok

def egTree104 : Tree := (.skew 1 2 1 (.node 1 egR104P0 (.node 2 (.skew 1 2 1 (.node 1 egR104P1 (.skew 1 2 1 (.node 1 egR104P2 (.skew 1 2 1 (.node 1 egR104P3 egR104P4)))))) egR104P5)))

theorem egTree104_ok : egTree104.okEnd 448 1000 3 (closeClass 104) EndSpec.endgame false (startE 104).1.1
    (startE 104).1.2.1 (startE 104).1.2.2 (startE 104).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR104P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR104P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR104P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR104P3_ok egR104P4_ok)))))) egR104P5_ok)))

def egTree106 : Tree := egR106P0

theorem egTree106_ok : egTree106.okEnd 448 1000 3 (closeClass 106) EndSpec.endgame false (startE 106).1.1
    (startE 106).1.2.1 (startE 106).1.2.2 (startE 106).2 0 none = true :=
  egR106P0_ok

def egTree108 : Tree := (.skew 1 2 1 (.node 1 egR108P0 (.node 2 (.skew 1 2 1 (.node 1 egR108P1 (.skew 1 2 1 (.node 1 egR108P2 (.node 1 egR108P3 (.node 2 egR108P4 egR108P5)))))) egR108P6)))

theorem egTree108_ok : egTree108.okEnd 448 1000 3 (closeClass 108) EndSpec.endgame false (startE 108).1.1
    (startE 108).1.2.1 (startE 108).1.2.2 (startE 108).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR108P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR108P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR108P2_ok (Tree.okEnd_node (by decide) egR108P3_ok (Tree.okEnd_node (by decide) egR108P4_ok egR108P5_ok)))))) egR108P6_ok)))

def egTree110 : Tree := egR110P0

theorem egTree110_ok : egTree110.okEnd 448 1000 3 (closeClass 110) EndSpec.endgame false (startE 110).1.1
    (startE 110).1.2.1 (startE 110).1.2.2 (startE 110).2 0 none = true :=
  egR110P0_ok

def egTree112 : Tree := (.skew 1 2 1 (.node 1 egR112P0 (.node 2 (.skew 1 2 1 (.node 1 egR112P1 (.skew 1 2 1 (.node 1 egR112P2 (.skew 1 2 1 (.node 1 egR112P3 (.skew 1 2 1 (.node 1 (.node 1 egR112P4 egR112P5) egR112P6)))))))) egR112P7)))

theorem egTree112_ok : egTree112.okEnd 448 1000 3 (closeClass 112) EndSpec.endgame false (startE 112).1.1
    (startE 112).1.2.1 (startE 112).1.2.2 (startE 112).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR112P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR112P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR112P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR112P3_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egR112P4_ok egR112P5_ok) egR112P6_ok)))))))) egR112P7_ok)))

def egTree114 : Tree := egR114P0

theorem egTree114_ok : egTree114.okEnd 448 1000 3 (closeClass 114) EndSpec.endgame false (startE 114).1.1
    (startE 114).1.2.1 (startE 114).1.2.2 (startE 114).2 0 none = true :=
  egR114P0_ok

def egTree116 : Tree := (.skew 1 2 1 (.node 1 egR116P0 (.node 2 (.skew 1 2 1 (.node 1 egR116P1 (.skew 1 2 1 (.node 1 egR116P2 egR116P3)))) egR116P4)))

theorem egTree116_ok : egTree116.okEnd 448 1000 3 (closeClass 116) EndSpec.endgame false (startE 116).1.1
    (startE 116).1.2.1 (startE 116).1.2.2 (startE 116).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR116P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR116P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR116P2_ok egR116P3_ok)))) egR116P4_ok)))

def egTree118 : Tree := egR118P0

theorem egTree118_ok : egTree118.okEnd 448 1000 3 (closeClass 118) EndSpec.endgame false (startE 118).1.1
    (startE 118).1.2.1 (startE 118).1.2.2 (startE 118).2 0 none = true :=
  egR118P0_ok

def egTree120 : Tree := (.skew 1 2 1 (.node 1 egR120P0 (.node 2 (.skew 1 2 1 (.node 1 egR120P1 (.skew 1 2 1 (.node 1 egR120P2 egR120P3)))) egR120P4)))

theorem egTree120_ok : egTree120.okEnd 448 1000 3 (closeClass 120) EndSpec.endgame false (startE 120).1.1
    (startE 120).1.2.1 (startE 120).1.2.2 (startE 120).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR120P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR120P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR120P2_ok egR120P3_ok)))) egR120P4_ok)))

def egTree122 : Tree := egR122P0

theorem egTree122_ok : egTree122.okEnd 448 1000 3 (closeClass 122) EndSpec.endgame false (startE 122).1.1
    (startE 122).1.2.1 (startE 122).1.2.2 (startE 122).2 0 none = true :=
  egR122P0_ok

def egTree124 : Tree := (.skew 1 2 1 (.node 1 egR124P0 (.node 2 (.skew 1 2 1 (.node 1 egR124P1 (.skew 1 2 1 (.node 1 egR124P2 (.node 1 egR124P3 (.node 2 egR124P4 egR124P5)))))) egR124P6)))

theorem egTree124_ok : egTree124.okEnd 448 1000 3 (closeClass 124) EndSpec.endgame false (startE 124).1.1
    (startE 124).1.2.1 (startE 124).1.2.2 (startE 124).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR124P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR124P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR124P2_ok (Tree.okEnd_node (by decide) egR124P3_ok (Tree.okEnd_node (by decide) egR124P4_ok egR124P5_ok)))))) egR124P6_ok)))

def egTree126 : Tree := egR126P0

theorem egTree126_ok : egTree126.okEnd 448 1000 3 (closeClass 126) EndSpec.endgame false (startE 126).1.1
    (startE 126).1.2.1 (startE 126).1.2.2 (startE 126).2 0 none = true :=
  egR126P0_ok

def egTree128 : Tree := (.skew 1 2 1 (.node 1 egR128P0 (.node 2 (.skew 1 2 1 (.node 1 egR128P1 (.skew 1 2 1 (.node 1 egR128P2 (.skew 1 2 1 (.node 1 egR128P3 (.skew 1 2 1 (.node 1 (.node 1 egR128P4 egR128P5) egR128P6)))))))) egR128P7)))

theorem egTree128_ok : egTree128.okEnd 448 1000 3 (closeClass 128) EndSpec.endgame false (startE 128).1.1
    (startE 128).1.2.1 (startE 128).1.2.2 (startE 128).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR128P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR128P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR128P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR128P3_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egR128P4_ok egR128P5_ok) egR128P6_ok)))))))) egR128P7_ok)))

def egTree130 : Tree := egR130P0

theorem egTree130_ok : egTree130.okEnd 448 1000 3 (closeClass 130) EndSpec.endgame false (startE 130).1.1
    (startE 130).1.2.1 (startE 130).1.2.2 (startE 130).2 0 none = true :=
  egR130P0_ok

def egTree132 : Tree := (.skew 1 2 1 (.node 1 egR132P0 (.node 2 (.skew 1 2 1 (.node 1 egR132P1 (.skew 1 2 1 (.node 1 egR132P2 egR132P3)))) egR132P4)))

theorem egTree132_ok : egTree132.okEnd 448 1000 3 (closeClass 132) EndSpec.endgame false (startE 132).1.1
    (startE 132).1.2.1 (startE 132).1.2.2 (startE 132).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR132P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR132P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR132P2_ok egR132P3_ok)))) egR132P4_ok)))

def egTree134 : Tree := egR134P0

theorem egTree134_ok : egTree134.okEnd 448 1000 3 (closeClass 134) EndSpec.endgame false (startE 134).1.1
    (startE 134).1.2.1 (startE 134).1.2.2 (startE 134).2 0 none = true :=
  egR134P0_ok

def egTree136 : Tree := (.skew 1 2 1 (.node 1 egR136P0 (.node 2 (.skew 1 2 1 (.node 1 egR136P1 (.skew 1 2 1 (.node 1 egR136P2 (.skew 1 2 1 (.node 1 egR136P3 egR136P4)))))) egR136P5)))

theorem egTree136_ok : egTree136.okEnd 448 1000 3 (closeClass 136) EndSpec.endgame false (startE 136).1.1
    (startE 136).1.2.1 (startE 136).1.2.2 (startE 136).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR136P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR136P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR136P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR136P3_ok egR136P4_ok)))))) egR136P5_ok)))

def egTree138 : Tree := egR138P0

theorem egTree138_ok : egTree138.okEnd 448 1000 3 (closeClass 138) EndSpec.endgame false (startE 138).1.1
    (startE 138).1.2.1 (startE 138).1.2.2 (startE 138).2 0 none = true :=
  egR138P0_ok

def egTree140 : Tree := (.skew 1 2 1 (.node 1 egR140P0 (.node 2 (.skew 1 2 1 (.node 1 egR140P1 (.skew 1 2 1 (.node 1 egR140P2 (.node 1 egR140P3 (.node 2 egR140P4 egR140P5)))))) egR140P6)))

theorem egTree140_ok : egTree140.okEnd 448 1000 3 (closeClass 140) EndSpec.endgame false (startE 140).1.1
    (startE 140).1.2.1 (startE 140).1.2.2 (startE 140).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR140P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR140P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR140P2_ok (Tree.okEnd_node (by decide) egR140P3_ok (Tree.okEnd_node (by decide) egR140P4_ok egR140P5_ok)))))) egR140P6_ok)))

def egTree142 : Tree := egR142P0

theorem egTree142_ok : egTree142.okEnd 448 1000 3 (closeClass 142) EndSpec.endgame false (startE 142).1.1
    (startE 142).1.2.1 (startE 142).1.2.2 (startE 142).2 0 none = true :=
  egR142P0_ok

def egTree144 : Tree := (.skew 1 2 1 (.node 1 egR144P0 (.node 2 (.skew 1 2 1 (.node 1 egR144P1 (.skew 1 2 1 (.node 1 egR144P2 (.skew 1 2 1 (.node 1 egR144P3 (.skew 1 2 1 (.node 1 egR144P4 egR144P5)))))))) egR144P6)))

theorem egTree144_ok : egTree144.okEnd 448 1000 3 (closeClass 144) EndSpec.endgame false (startE 144).1.1
    (startE 144).1.2.1 (startE 144).1.2.2 (startE 144).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR144P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR144P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR144P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR144P3_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR144P4_ok egR144P5_ok)))))))) egR144P6_ok)))

def egTree146 : Tree := egR146P0

theorem egTree146_ok : egTree146.okEnd 448 1000 3 (closeClass 146) EndSpec.endgame false (startE 146).1.1
    (startE 146).1.2.1 (startE 146).1.2.2 (startE 146).2 0 none = true :=
  egR146P0_ok

def egTree148 : Tree := (.skew 1 2 1 (.node 1 egR148P0 (.node 2 (.skew 1 2 1 (.node 1 egR148P1 (.skew 1 2 1 (.node 1 egR148P2 egR148P3)))) egR148P4)))

theorem egTree148_ok : egTree148.okEnd 448 1000 3 (closeClass 148) EndSpec.endgame false (startE 148).1.1
    (startE 148).1.2.1 (startE 148).1.2.2 (startE 148).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR148P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR148P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR148P2_ok egR148P3_ok)))) egR148P4_ok)))

def egTree150 : Tree := egR150P0

theorem egTree150_ok : egTree150.okEnd 448 1000 3 (closeClass 150) EndSpec.endgame false (startE 150).1.1
    (startE 150).1.2.1 (startE 150).1.2.2 (startE 150).2 0 none = true :=
  egR150P0_ok

def egTree152 : Tree := (.skew 1 2 1 (.node 1 egR152P0 (.node 2 (.skew 1 2 1 (.node 1 egR152P1 (.skew 1 2 1 (.node 1 egR152P2 (.skew 1 2 1 (.node 1 egR152P3 egR152P4)))))) egR152P5)))

theorem egTree152_ok : egTree152.okEnd 448 1000 3 (closeClass 152) EndSpec.endgame false (startE 152).1.1
    (startE 152).1.2.1 (startE 152).1.2.2 (startE 152).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR152P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR152P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR152P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR152P3_ok egR152P4_ok)))))) egR152P5_ok)))

def egTree154 : Tree := egR154P0

theorem egTree154_ok : egTree154.okEnd 448 1000 3 (closeClass 154) EndSpec.endgame false (startE 154).1.1
    (startE 154).1.2.1 (startE 154).1.2.2 (startE 154).2 0 none = true :=
  egR154P0_ok

def egTree156 : Tree := (.skew 1 2 1 (.node 1 egR156P0 (.node 2 (.skew 1 2 1 (.node 1 egR156P1 (.skew 1 2 1 (.node 1 egR156P2 (.node 1 egR156P3 (.node 2 egR156P4 egR156P5)))))) egR156P6)))

theorem egTree156_ok : egTree156.okEnd 448 1000 3 (closeClass 156) EndSpec.endgame false (startE 156).1.1
    (startE 156).1.2.1 (startE 156).1.2.2 (startE 156).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR156P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR156P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR156P2_ok (Tree.okEnd_node (by decide) egR156P3_ok (Tree.okEnd_node (by decide) egR156P4_ok egR156P5_ok)))))) egR156P6_ok)))

def egTree158 : Tree := egR158P0

theorem egTree158_ok : egTree158.okEnd 448 1000 3 (closeClass 158) EndSpec.endgame false (startE 158).1.1
    (startE 158).1.2.1 (startE 158).1.2.2 (startE 158).2 0 none = true :=
  egR158P0_ok

def egTree160 : Tree := (.skew 1 2 1 (.node 1 egR160P0 (.node 2 (.skew 1 2 1 (.node 1 egR160P1 (.skew 1 2 1 (.node 1 egR160P2 (.skew 1 2 1 (.node 1 egR160P3 (.skew 1 2 1 (.node 1 (.node 1 (.node 1 egR160P4 (.node 1 (.node 2 egR160P5 egR160P6) egR160P7)) egR160P8) egR160P9)))))))) egR160P10)))

theorem egTree160_ok : egTree160.okEnd 448 1000 3 (closeClass 160) EndSpec.endgame false (startE 160).1.1
    (startE 160).1.2.1 (startE 160).1.2.2 (startE 160).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR160P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR160P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR160P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR160P3_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egR160P4_ok (Tree.okEnd_node (by decide) (Tree.okEnd_node (by decide) egR160P5_ok egR160P6_ok) egR160P7_ok)) egR160P8_ok) egR160P9_ok)))))))) egR160P10_ok)))

def egTree162 : Tree := egR162P0

theorem egTree162_ok : egTree162.okEnd 448 1000 3 (closeClass 162) EndSpec.endgame false (startE 162).1.1
    (startE 162).1.2.1 (startE 162).1.2.2 (startE 162).2 0 none = true :=
  egR162P0_ok

def egTree164 : Tree := (.skew 1 2 1 (.node 1 egR164P0 (.node 2 (.skew 1 2 1 (.node 1 egR164P1 (.skew 1 2 1 (.node 1 egR164P2 egR164P3)))) egR164P4)))

theorem egTree164_ok : egTree164.okEnd 448 1000 3 (closeClass 164) EndSpec.endgame false (startE 164).1.1
    (startE 164).1.2.1 (startE 164).1.2.2 (startE 164).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR164P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR164P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR164P2_ok egR164P3_ok)))) egR164P4_ok)))

def egTree166 : Tree := egR166P0

theorem egTree166_ok : egTree166.okEnd 448 1000 3 (closeClass 166) EndSpec.endgame false (startE 166).1.1
    (startE 166).1.2.1 (startE 166).1.2.2 (startE 166).2 0 none = true :=
  egR166P0_ok

def egTree168 : Tree := (.skew 1 2 1 (.node 1 egR168P0 (.node 2 (.skew 1 2 1 (.node 1 egR168P1 (.skew 1 2 1 (.node 1 egR168P2 (.skew 1 2 1 (.node 1 egR168P3 egR168P4)))))) egR168P5)))

theorem egTree168_ok : egTree168.okEnd 448 1000 3 (closeClass 168) EndSpec.endgame false (startE 168).1.1
    (startE 168).1.2.1 (startE 168).1.2.2 (startE 168).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR168P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR168P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR168P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR168P3_ok egR168P4_ok)))))) egR168P5_ok)))

def egTree170 : Tree := egR170P0

theorem egTree170_ok : egTree170.okEnd 448 1000 3 (closeClass 170) EndSpec.endgame false (startE 170).1.1
    (startE 170).1.2.1 (startE 170).1.2.2 (startE 170).2 0 none = true :=
  egR170P0_ok

def egTree172 : Tree := (.skew 1 2 1 (.node 1 egR172P0 (.node 2 (.skew 1 2 1 (.node 1 egR172P1 (.skew 1 2 1 (.node 1 egR172P2 (.node 1 egR172P3 (.node 2 egR172P4 egR172P5)))))) egR172P6)))

theorem egTree172_ok : egTree172.okEnd 448 1000 3 (closeClass 172) EndSpec.endgame false (startE 172).1.1
    (startE 172).1.2.1 (startE 172).1.2.2 (startE 172).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR172P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR172P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR172P2_ok (Tree.okEnd_node (by decide) egR172P3_ok (Tree.okEnd_node (by decide) egR172P4_ok egR172P5_ok)))))) egR172P6_ok)))

def egTree174 : Tree := egR174P0

theorem egTree174_ok : egTree174.okEnd 448 1000 3 (closeClass 174) EndSpec.endgame false (startE 174).1.1
    (startE 174).1.2.1 (startE 174).1.2.2 (startE 174).2 0 none = true :=
  egR174P0_ok

def egTree176 : Tree := (.skew 1 2 1 (.node 1 egR176P0 (.node 2 (.skew 1 2 1 (.node 1 egR176P1 (.skew 1 2 1 (.node 1 egR176P2 (.skew 1 2 1 (.node 1 egR176P3 (.skew 1 2 1 (.node 1 egR176P4 egR176P5)))))))) egR176P6)))

theorem egTree176_ok : egTree176.okEnd 448 1000 3 (closeClass 176) EndSpec.endgame false (startE 176).1.1
    (startE 176).1.2.1 (startE 176).1.2.2 (startE 176).2 0 none = true :=
  (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR176P0_ok (Tree.okEnd_node (by decide) (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR176P1_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR176P2_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR176P3_ok (Tree.okEnd_skew (by decide) (by decide) (by decide) (Tree.okEnd_node (by decide) egR176P4_ok egR176P5_ok)))))))) egR176P6_ok)))

/-- The trees for the even R < 178. -/
def smallTrees : List (Nat × Tree) := [(2, egTree2), (4, egTree4), (6, egTree6), (8, egTree8), (10, egTree10), (12, egTree12), (14, egTree14), (16, egTree16), (18, egTree18), (20, egTree20), (22, egTree22), (24, egTree24), (26, egTree26), (28, egTree28), (30, egTree30), (32, egTree32), (34, egTree34), (36, egTree36), (38, egTree38), (40, egTree40), (42, egTree42), (44, egTree44), (46, egTree46), (48, egTree48), (50, egTree50), (52, egTree52), (54, egTree54), (56, egTree56), (58, egTree58), (60, egTree60), (62, egTree62), (64, egTree64), (66, egTree66), (68, egTree68), (70, egTree70), (72, egTree72), (74, egTree74), (76, egTree76), (78, egTree78), (80, egTree80), (82, egTree82), (84, egTree84), (86, egTree86), (88, egTree88), (90, egTree90), (92, egTree92), (94, egTree94), (96, egTree96), (98, egTree98), (100, egTree100), (102, egTree102), (104, egTree104), (106, egTree106), (108, egTree108), (110, egTree110), (112, egTree112), (114, egTree114), (116, egTree116), (118, egTree118), (120, egTree120), (122, egTree122), (124, egTree124), (126, egTree126), (128, egTree128), (130, egTree130), (132, egTree132), (134, egTree134), (136, egTree136), (138, egTree138), (140, egTree140), (142, egTree142), (144, egTree144), (146, egTree146), (148, egTree148), (150, egTree150), (152, egTree152), (154, egTree154), (156, egTree156), (158, egTree158), (160, egTree160), (162, egTree162), (164, egTree164), (166, egTree166), (168, egTree168), (170, egTree170), (172, egTree172), (174, egTree174), (176, egTree176)]

theorem small_trees_ok :
    ∀ p ∈ smallTrees, p.2.okEnd 448 1000 3 (closeClass p.1) EndSpec.endgame false (startE p.1).1.1
      (startE p.1).1.2.1 (startE p.1).1.2.2 (startE p.1).2 0 none = true :=
  List.forall_mem_cons.2 ⟨egTree2_ok, List.forall_mem_cons.2 ⟨egTree4_ok, List.forall_mem_cons.2 ⟨egTree6_ok, List.forall_mem_cons.2 ⟨egTree8_ok, List.forall_mem_cons.2 ⟨egTree10_ok, List.forall_mem_cons.2 ⟨egTree12_ok, List.forall_mem_cons.2 ⟨egTree14_ok, List.forall_mem_cons.2 ⟨egTree16_ok, List.forall_mem_cons.2 ⟨egTree18_ok, List.forall_mem_cons.2 ⟨egTree20_ok, List.forall_mem_cons.2 ⟨egTree22_ok, List.forall_mem_cons.2 ⟨egTree24_ok, List.forall_mem_cons.2 ⟨egTree26_ok, List.forall_mem_cons.2 ⟨egTree28_ok, List.forall_mem_cons.2 ⟨egTree30_ok, List.forall_mem_cons.2 ⟨egTree32_ok, List.forall_mem_cons.2 ⟨egTree34_ok, List.forall_mem_cons.2 ⟨egTree36_ok, List.forall_mem_cons.2 ⟨egTree38_ok, List.forall_mem_cons.2 ⟨egTree40_ok, List.forall_mem_cons.2 ⟨egTree42_ok, List.forall_mem_cons.2 ⟨egTree44_ok, List.forall_mem_cons.2 ⟨egTree46_ok, List.forall_mem_cons.2 ⟨egTree48_ok, List.forall_mem_cons.2 ⟨egTree50_ok, List.forall_mem_cons.2 ⟨egTree52_ok, List.forall_mem_cons.2 ⟨egTree54_ok, List.forall_mem_cons.2 ⟨egTree56_ok, List.forall_mem_cons.2 ⟨egTree58_ok, List.forall_mem_cons.2 ⟨egTree60_ok, List.forall_mem_cons.2 ⟨egTree62_ok, List.forall_mem_cons.2 ⟨egTree64_ok, List.forall_mem_cons.2 ⟨egTree66_ok, List.forall_mem_cons.2 ⟨egTree68_ok, List.forall_mem_cons.2 ⟨egTree70_ok, List.forall_mem_cons.2 ⟨egTree72_ok, List.forall_mem_cons.2 ⟨egTree74_ok, List.forall_mem_cons.2 ⟨egTree76_ok, List.forall_mem_cons.2 ⟨egTree78_ok, List.forall_mem_cons.2 ⟨egTree80_ok, List.forall_mem_cons.2 ⟨egTree82_ok, List.forall_mem_cons.2 ⟨egTree84_ok, List.forall_mem_cons.2 ⟨egTree86_ok, List.forall_mem_cons.2 ⟨egTree88_ok, List.forall_mem_cons.2 ⟨egTree90_ok, List.forall_mem_cons.2 ⟨egTree92_ok, List.forall_mem_cons.2 ⟨egTree94_ok, List.forall_mem_cons.2 ⟨egTree96_ok, List.forall_mem_cons.2 ⟨egTree98_ok, List.forall_mem_cons.2 ⟨egTree100_ok, List.forall_mem_cons.2 ⟨egTree102_ok, List.forall_mem_cons.2 ⟨egTree104_ok, List.forall_mem_cons.2 ⟨egTree106_ok, List.forall_mem_cons.2 ⟨egTree108_ok, List.forall_mem_cons.2 ⟨egTree110_ok, List.forall_mem_cons.2 ⟨egTree112_ok, List.forall_mem_cons.2 ⟨egTree114_ok, List.forall_mem_cons.2 ⟨egTree116_ok, List.forall_mem_cons.2 ⟨egTree118_ok, List.forall_mem_cons.2 ⟨egTree120_ok, List.forall_mem_cons.2 ⟨egTree122_ok, List.forall_mem_cons.2 ⟨egTree124_ok, List.forall_mem_cons.2 ⟨egTree126_ok, List.forall_mem_cons.2 ⟨egTree128_ok, List.forall_mem_cons.2 ⟨egTree130_ok, List.forall_mem_cons.2 ⟨egTree132_ok, List.forall_mem_cons.2 ⟨egTree134_ok, List.forall_mem_cons.2 ⟨egTree136_ok, List.forall_mem_cons.2 ⟨egTree138_ok, List.forall_mem_cons.2 ⟨egTree140_ok, List.forall_mem_cons.2 ⟨egTree142_ok, List.forall_mem_cons.2 ⟨egTree144_ok, List.forall_mem_cons.2 ⟨egTree146_ok, List.forall_mem_cons.2 ⟨egTree148_ok, List.forall_mem_cons.2 ⟨egTree150_ok, List.forall_mem_cons.2 ⟨egTree152_ok, List.forall_mem_cons.2 ⟨egTree154_ok, List.forall_mem_cons.2 ⟨egTree156_ok, List.forall_mem_cons.2 ⟨egTree158_ok, List.forall_mem_cons.2 ⟨egTree160_ok, List.forall_mem_cons.2 ⟨egTree162_ok, List.forall_mem_cons.2 ⟨egTree164_ok, List.forall_mem_cons.2 ⟨egTree166_ok, List.forall_mem_cons.2 ⟨egTree168_ok, List.forall_mem_cons.2 ⟨egTree170_ok, List.forall_mem_cons.2 ⟨egTree172_ok, List.forall_mem_cons.2 ⟨egTree174_ok, List.forall_mem_cons.2 ⟨egTree176_ok, fun _ h => nomatch h⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩⟩

theorem small_trees_cover :
    ((List.range 88).all fun r => smallTrees.any fun (p : Nat × Tree) => p.1 == 2 * (r + 1)) = true := by
  decide +kernel

/-- **The endgame, for the machine.**  For every even R ≥ 2 and every phase-0 pass start — walls at a, b and
c = E − R − 1, width E, with a odd, b even, E even and every gap at least 448 — either R is in the closing set and
the left countdown L₁ = 147 b + 280 E − 392 c − 578 is in R's class (`closeClass`), or the machine runs n rounds
without halting, reaching the round start that `roundsZ` computes, every end meeting on the way is at distance at
least 3 (no close), and the run ends at an end event (`EndEvent`): it left phase 0 (round 1 not G B W or round 2 not
G M B) or its end meetings left the halving chain, at a round start that is not three walls; or it is at a landing of
the loop's chain (`Landing`): three walls with a odd, b even and width W′ ≡ 0 mod 4, right end R′ even and at least 2,
after a full pass (R′ = R/16, L₁′ = L₁/64, W′ = E + 24), a half pass (from E ≡ 2 mod 4; R′ = R/2, W′ = E + 6) or a
break of the chain at round 7 (W′ = E + 24), with the exact maps of `StepMap`.  None of these holds after zero rounds
(`not_endEvent_zero`). -/
theorem endgame_stretch (R : Nat) (hR : R % 2 = 0) (hR2 : 2 ≤ R)
    (a b E : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) (hE : E % 2 = 0)
    (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) :
    (∃ m c, closeClass R = some (m, c) ∧ loopL1 b (E - R - 1) E % m = c) ∨
    ∃ n kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = some (roundStart ms' W') ∧
      roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
      (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
      EndEvent E R (loopL1 b (E - R - 1) E) n (meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E)
        ms' W' := by
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
    have hf : symStartE.2.Ag y E R (loopL1 b (E - R - 1) E) := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [agN, y, symStartE, YForm.eval, dot]; omega
      · simp only [agN, y, symStartE, YForm.eval, dot]; omega
      · simp only [symStartE, eval_L1Form, loopL1]
        simp only [y, YForm.eval, YForm.sub, YForm.add, YForm.neg, YForm.addc, addL, smulL, List.map, dot]
        omega
    rcases Tree.soundEnd 448 1000 4 none .endgame symTree false _ _ _ _ 0 none sym_tree_ok y rfl hy _ _ E R
        (loopL1 b (E - R - 1) E) [] hs hW hf (fun h => by cases h) (fun _ h => by cases h) with
      ⟨_, _, h, -⟩ | h
    · cases h
    · simp only [List.nil_append, Nat.zero_add] at h
      exact Or.inr h
  · -- the tree for R
    have hcov := small_trees_cover
    rw [List.all_eq_true] at hcov
    have hr := hcov (R / 2 - 1) (by simp only [List.mem_range]; omega)
    have e : 2 * (R / 2 - 1 + 1) = R := by omega
    rw [e, List.any_eq_true] at hr
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
    have hf : (startE R').2.Ag y E R' (loopL1 b (E - R' - 1) E) := by
      refine ⟨?_, ?_, ?_⟩
      · simp only [agN, y, startE, YForm.eval, dot]; omega
      · simp [agN, startE, YForm.const, YForm.eval]
      · simp only [startE, eval_L1Form, loopL1]
        simp only [y, YForm.eval, YForm.addc, dot]
        omega
    rcases Tree.soundEnd 448 1000 3 (closeClass R') .endgame t false _ _ _ _ 0 none ht y rfl hy _ _ E R'
        (loopL1 b (E - R' - 1) E) [] hs hW hf (fun h => by cases h) (fun _ h => by cases h) with h | h
    · exact Or.inl h
    · simp only [List.nil_append, Nat.zero_add] at h
      exact Or.inr h

/-- **No close from a right end outside the closing set.**  For R outside {2, 4, 8, 16, 24, 32, 48, 64, 176}, the
stretch of `endgame_stretch` always runs: close-free, to an end event. -/
theorem endgame_no_close (R : Nat) (hR : R % 2 = 0) (hR2 : 2 ≤ R) (hS : closingSet.contains R = false)
    (a b E : Nat) (ha : a % 2 = 1) (hb : b % 2 = 0) (hE : E % 2 = 0)
    (h1 : 448 ≤ a) (h2 : a + 448 ≤ b) (h3 : b + 448 + R + 1 ≤ E) :
    ∃ n kk ms' W', steps kk (roundStart [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E) = some (roundStart ms' W') ∧
      roundsZ 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E = .newRound ms' W' ∧
      (∀ d ∈ meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E, 3 ≤ d) ∧
      EndEvent E R (loopL1 b (E - R - 1) E) n (meetsRounds 1000 n [⟨.W, a⟩, ⟨.W, b⟩, ⟨.W, E - R - 1⟩] E)
        ms' W' := by
  rcases endgame_stretch R hR hR2 a b E ha hb hE h1 h2 h3 with ⟨_, _, hc, -⟩ | h
  · rw [closeClass_closing hc] at hS; cases hS
  · exact h

/-- L₁ ≡ 3 (mod 7) at every pass start, so each class of `closeClasses` is a class modulo 7 m: 10 mod 14 (R = 2, 4),
24 mod 56 (8), 192 mod 224 (16), 416 mod 448 (24), 192 mod 448 (32) and 640 mod 896 (48, 64, 176). -/
theorem loopL1_mod7 (b c E : Nat) : loopL1 b c E % 7 = 3 := by
  unfold loopL1; omega
