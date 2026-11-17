import BusyBeaver.BB6.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB
import BusyBeaver.BB6.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA
import BusyBeaver.BB6.M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA
import BusyBeaver.BB6.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE
import BusyBeaver.BB6.M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH
import BusyBeaver.BB6.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
import BusyBeaver.BB6.M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH
import BusyBeaver.BB6.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC
import BusyBeaver.BB6.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA
import BusyBeaver.BB6.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE
import BusyBeaver.BB6.M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD
import BusyBeaver.BB6.M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC
import BusyBeaver.BB6.M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA
import BusyBeaver.BB6.M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC
import BusyBeaver.BB6.M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC
open Turing
#check @BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LB_1LC0RE_1LA1LD_0LCHHH_0RB0RF_1RE1RB.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LC_0LC1RF_1LE1RD_0RC1RC_0LA1LA_HHH1RA.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LFHHH_0LA1LA.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LD_1LC0RA_1RA1LB_1LA1LE_1RF0LC_HHH0RE.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LD_1RC1RF_1LA0RA_0LA0LE_1LD1LA_0RBHHH.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0LE_1LC1RA_1RA1LD_0LC0LA_0RE1RF_0RCHHH.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB0RE_1LC0RA_1RF0RD_HHH1LE_0LB1LE_1LE1RC.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1LC_1RC0RF_1RD0LB_1RE0LD_1LFHHH_0RA1LA.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1LE_0LC0LB_1RD1LC_1RD1RA_1RF0LA_HHH1RE.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1LE_1LB1LC_1RD0LE_HHH0RB_1RF1LA_0RA0RD.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1LE_1LC0RA_0RF0LD_1LE1LA_1RC0LB_HHH1RC.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1LF_0RC1RD_1LA1LD_1LE0RA_HHH1LC_0LA1LA.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1RA_0RC1RC_1LD0LF_0LE1LE_1RA0LB_HHH0LC.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
#check @BusyBeaver.M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC.isHalt_iff_acceleration
#print axioms BusyBeaver.M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC.isHalt_iff_acceleration
#eval IO.println ("TABLE M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC " ++ String.intercalate "_" ((List.finRange 6).map fun q => String.join ((List.finRange 2).map fun a => match BusyBeaver.M_1RB1RD_1LC0RD_1RF1RB_1LE0RA_0LB0LE_HHH0RC.machine.transition q a with | none => "---" | some (w, d, s) => toString w.val ++ (match d with | .left => "L" | .right => "R") ++ toString (Char.ofNat (65 + s.val)))))
