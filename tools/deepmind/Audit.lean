import BusyBeaver.BB6.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH
import BusyBeaver.BB6.Halt.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA
import BusyBeaver.BB6.Halt.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH
import BusyBeaver.BB6.Halt.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH
import BusyBeaver.BB6.Halt.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH
import BusyBeaver.BB6.NonHalt.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA
import BusyBeaver.BB6.NonHalt.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA
import BusyBeaver.BB6.NonHalt.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD
import BusyBeaver.BB6.NonHalt.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF
import BusyBeaver.BB6.NonHalt.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH
import BusyBeaver.BB6.NonHalt.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF
open Turing
#check @BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.is_not_halt
#print axioms BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.is_not_halt
#eval IO.println ("TABLE M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LF_1RC0RA_1LD0RB_0LE0LC_0LA0LC_0LBHHH.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.is_halt
#print axioms BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.is_halt
#eval IO.println ("TABLE M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1RC_1LC0LF_1RF0LD_0RE1LB_1RCHHH_1LD0RA.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.is_halt
#print axioms BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.is_halt
#eval IO.println ("TABLE M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1RF_0RC0RE_0RD1RA_1LE0LA_1LB0LD_0RDHHH.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.is_halt
#print axioms BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.is_halt
#eval IO.println ("TABLE M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LC_1LC0RE_1RF1LD_1LA0LB_1RD1RA_1LBHHH.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.is_halt
#print axioms BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.is_halt
#eval IO.println ("TABLE M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0RE_1RC0RA_0LD0LB_0LA1LE_1LC1LF_0LAHHH.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA.is_not_halt
#print axioms BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA.is_not_halt
#eval IO.println ("TABLE M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0RA_0RC0LE_1LD1RF_1LB1RD_1LD1LE_HHH1RA.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.is_not_halt
#print axioms BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.is_not_halt
#eval IO.println ("TABLE M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0RA_0RC0LD_1LA1RF_1LE1LD_1LB1RE_HHH1RA.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD.is_not_halt
#print axioms BusyBeaver.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD.is_not_halt
#eval IO.println ("TABLE M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1RA_0LC0RA_1RC1LD_0LB1LE_1LF0RC_HHH0LD.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.is_not_halt
#print axioms BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.is_not_halt
#eval IO.println ("TABLE M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1RA_1RC1LB_0LD0RA_1RF1LE_HHH1LF_1LC0LF.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.is_not_halt
#print axioms BusyBeaver.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.is_not_halt
#eval IO.println ("TABLE M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0RA_1RC0LC_0LD1RF_1RA1LE_1LD0LB_0REHHH.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.is_not_halt
#print axioms BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.is_not_halt
#eval IO.println ("TABLE M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LC_1LC0RB_0LE0LD_1LCHHH_0RA1LF_1LA1LF.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
