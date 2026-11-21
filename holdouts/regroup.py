#!/usr/bin/env python3
"""Regroup the undecided holdouts into families that one proof technique could settle together (20 November 2026).

Writes holdouts/families.json (read by build_pages.py for the index page) and holdouts/FAMILIES.md.

How the families are made:

1. The undecided machines are the ones whose standing on the index is open, cryptid or pr (an outside proof that is
   not compiled here), read with build_pages.standing.
2. Table distance: for every pair of the 608 machines, the fewest transitions that differ between the two tables,
   minimised over the 720 renamings of the states and the mirror image (the start state is ignored, an undefined
   transition counts as a value of its own). Distance 0 is the same table from another start; distance 1 is one
   transition changed. Single-linkage clusters at distance <= 1 are the "table sets".
3. Families are table sets joined by a shared mechanism, read from each machine's own description (status.json
   summary) and the community tracker's class. The rules are in FAMILIES below: a family is a union of table sets
   (given by one member machine) and of machines whose description matches a pattern within a tracker class.
4. Machines left over keep the family of the 13 November plan (F01 to F12, project file plan/families.json), copied
   into OLD_FAMILY below so that the script does not need the project files.

Needs numpy (only this script; the page build does not).
"""
import collections
import json
import os
import re
import sys
from itertools import permutations

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import build_pages as bp  # noqa: E402

ASOF = "20 November 2026"

# ---------------------------------------------------------------- table distance


def parse(m):
    out = []
    for blk in m.split("_"):
        for t in (blk[:3], blk[3:]):
            out.append(None if t == "---" else (int(t[0]), t[1], "ABCDEF".index(t[2])))
    return out


def enc(tr):
    return [-1 if t is None else t[0] * 100 + (t[1] == "R") * 10 + t[2] for t in tr]


def relabel(tr, p, mirror):
    new = [None] * 12
    for s in range(6):
        for r in range(2):
            t = tr[2 * s + r]
            if t is not None:
                mv = t[1] if not mirror else ("L" if t[1] == "R" else "R")
                t = (t[0], mv, p[t[2]])
            new[2 * p[s] + r] = t
    return new


def distances(machines):
    perms = list(permutations(range(6)))
    T = [parse(m) for m in machines]
    base = np.array([enc(t) for t in T], dtype=np.int16)
    allr = np.array([[enc(relabel(t, p, mir)) for p in perms for mir in (0, 1)] for t in T], dtype=np.int16)
    D = np.zeros((len(machines), len(machines)), dtype=np.int8)
    for i in range(len(machines)):
        D[i] = (allr != base[i][None, None, :]).sum(axis=2).min(axis=1)
    return D


def table_sets(machines, D, th=1):
    par = list(range(len(machines)))

    def f(x):
        while par[x] != x:
            par[x] = par[par[x]]
            x = par[x]
        return x
    for i in range(len(machines)):
        for j in range(i + 1, len(machines)):
            if D[i, j] <= th:
                par[f(i)] = f(j)
    groups = collections.defaultdict(list)
    for i in range(len(machines)):
        groups[f(i)].append(machines[i])
    return {m: min(g) for g in groups.values() for m in g}  # machine -> the set's smallest member, as its name


# ---------------------------------------------------------------- the families

# Each family: id, rank (1 = attack first), name, members (table sets named by one member, and/or description patterns
# within a tracker class), mechanism, technique, why ranked here. Text uses full machine names.
FAMILIES = [
    dict(id="R01", name="Base-5 marker counter on one five-state core (F05)",
         sets=["1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA---", "1RB1LF_1LC0RD_0LD0LC_1RE0LA_0RA0RC_0RE---"],
         old=["F05"],
         mechanism="Forty machines are one five-state core, `1RB0LC_0RC0RB_1LD0RE_0LE?LF_1LA0LB_??---` in frame A, "
                   "differing in D1, F0 and the start; five more use the same core with E1 or F0 changed. The tape is a "
                   "list of 0010-blocks run like a nested base-5 counter; a machine can halt only at an F-event "
                   "(the detour through F) that reads a 1.",
         known="Lean proves the visit law, its closed form and a conservation law for all 40 on each machine's own "
               "table (`Family.lean` in each folder); the exact block-list map ran 37 of them to 10^200 steps, every "
               "F-event reading 0. The same-run step is done: ten twin pairs and seven start-twin pairs "
               "(`EQUIVALENCES.md`; `Twin.lean`, `StartTwin.lean`) put 31 of the 40 into 14 classes, so the 40 are "
               "23 questions, and a recheck of all 40 block lists at every left-end event to 10^30 steps "
               "(21 November) found no further pair: the twelve start-E machines part from each other and from "
               "the start-A ones by the sixth left-end event.",
         technique="One invariant on the shared core: show that an F-event never reads 1, i.e. that the drift "
                   "b(i+1) - 5·b(i) is never within a few hundred of 0 when block i runs out. Clean visits keep every "
                   "drift fixed, so only the drifts made at merges matter. A proof on the core settles all 40 at once.",
         odds="low: the drifts made at merges behave like differences of unrelated large numbers. To 10^100 steps "
              "the 599 drifts of 1RB0LC_0RC0RB_1LD0RE_0LE0LF_1LA0LB_0RA--- are all even but take every residue "
              "mod 9 and mod 25 (122 of 125 mod 125), and |b(i+1) - 5·b(i)| / b(i) gets as low as 0.015, so "
              "neither a congruence nor a ratio bound is kept. A proof would have to show that a chaotic integer "
              "process misses a thin set, a Collatz-type statement. Heuristically they do not halt: every drift "
              "made after the 30th left-end event is above 8·10^6 in size, against the few hundred a halt needs."),
    dict(id="R02", name="Clock and word: a block grows in doubling time while a word map runs 2^k times",
         pattern=(r"\bclock\b|doubling time|2\^k applications|2<sup>k</sup> applications", "Shift-overflow"),
         mechanism="A block at one end grows by 2, 3 or 4 cells per tick and tick k applies one word map P (one trip "
                   "of the head) 2^k times to the word beside it; halting is possible only when a rebuild of the end "
                   "goes wrong. Six tables.",
         known="The clock lemma (block growth and the 2^k trips, whenever the trips return) is proved in Lean for "
               "every k on six of them, for example `1RB0RA_1RC0RC_1LD0LE_1RA1LC_1LC0LF_0LC---` and "
               "`1RB---_1RC1RF_1LD1RE_1LB1LD_0RB0RC_1RA0LF`. DeepMind's file lists three as cryptids.",
         technique="Close the word map alone: find a regular language of words that P maps into itself and that "
                   "never triggers the halting rebuild (a SAT search over automata on the word, much smaller than the "
                   "whole-tape search that failed in `satctl.json`), then combine it with the clock lemma in Lean. "
                   "The same pipeline serves every member; only P changes.",
         odds="medium: the remaining question is one finite-state map per machine, not a counter race; the three "
              "DeepMind cryptids are the least likely."),
    dict(id="R03", name="Blocks of 10s split by 01100: one table core with cursors that triple blocks",
         sets=["1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---", "1RB0LE_1RC0LB_1RD1RF_1RE0RB_1LA0RD_0RE---"],
         mechanism="Twelve machines one transition apart (tracker class Chaotic Bell Class 3) and three neighbours "
                   "two transitions away: a list of blocks (10)^n separated by 01100 or single 1s, with a cursor or "
                   "reflector that walks through it and triples or moves blocks, on a budget held in the first block.",
         known="Round trips and the moving reflector are proved in Lean for several, for example "
               "`1RB0LC_1RC0RA_1LA0LD_1LE0RB_1RD1LF_0LA---` and `1RB0RC_1LC0LD_1RA0LB_1LE0RA_1RD1LF_0LC---`; "
               "`1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---` has a halting tape of the same form proved in Lean.",
         technique="Do for this core what `Family.lean` did for F05: one generated Lean library of the shared rules "
                   "proved on every member's table, then an exact block-list map per member run far to hunt for "
                   "halts (the budget rules make a halt plausible).",
         odds="medium: shared rules make the library cheap; whether the runs halt is unknown."),
    dict(id="R04", name="Base-4 counters with countdown timers (Skelet 1-like)",
         pattern=(r"base-4|base 4", "Skelet|Shift|Unknown"),
         sets=["1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE", "1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD",
               "1RB1LD_1RC1RF_1LA1RD_1RE0LB_---0RA_0LA1RC", "1RB0RE_1LC1LF_1RA1LD_0LB---_1RF1LE_0LB0RA"],
         drop=["1RB0LB_1LC1RE_1LA1LD_0RB1LF_1LA0RC_---1LC", "1RB1RF_1LC1RD_1RA1LD_1RE0LA_---0RC_0LC1RB"],
         mechanism="A base-4 counter whose digits sit between blocks, and blocks that lose 4^i (or 9, 24, 96, ...) "
                   "units per visit like timers; when a timer runs out digits fuse or a level is rebuilt.",
         known="Digit and sweep rules are proved in Lean for several; for `1RB1RE_1LC0RC_1RA1LD_1RB0LA_0LC1RF_---1RD` "
               "and `1RB1RE_1LC0RF_1LA0LD_1LE1LC_0RA0LC_1RA---` Lean proves that tapes of the same shape with short "
               "timers halt. `1RB1LF_0RC1RC_1LD0RD_0LE0LA_1RA0LB_---1LD` halts iff its twin "
               "`1RB1LE_1RC1LF_0RD1RD_1LE0RE_0LA0LB_---1LE` halts from state B (Lean). "
               "`1RB0RB_0LC1RA_1RD1LC_1LA1LE_1LF0LD_---0LA` has a halting proof in busycoq PR 64 (not compiled here).",
         technique="Halt hunting with exact odometer jumps (the PR 83 / PR 89 method: b^k ticks in one operation, "
                   "then an exact executor to the halt). In the week of 13 November this kind of family (F06) gave half of all decisions, "
                   "all of them halting.",
         odds="medium-high for halts: short-timer tapes halt, so a run that reaches one is a proof."),
    dict(id="R05", name="Cellular-automaton sweeps: running parity and Sierpinski triangles",
         sets=["1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF", "1RB---_0RC1RD_1LA0LA_1LE0RB_1LF1LE_1LC0LD"],
         extra=["1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB"],
         mechanism="Each sweep rewrites the tape like one step of a one-dimensional cellular automaton. In "
                   "`1RB0RE_0RC---_1LD1LE_1LE1LD_1RF0LC_1RA1RF` and its slower twin "
                   "`1RB0RE_1RC0RC_1LD---_0LB1LE_1RF0LD_1RA1RF` a leftward sweep replaces a binary word by its running "
                   "parity, so the space-time diagram is Pascal's triangle mod 2; "
                   "`1RB1LB_1LC0RD_0LE1LA_0RF1RA_1LE0LA_---0RB` runs rule 102 (XOR); the others draw Sierpinski-like "
                   "triangles on blocks of 1s.",
         known="Two pairs run through the same tapes (observed); for the XOR machine the bulk-merge trigger is known "
               "and was last seen at 4.07·10^6 steps in a 10^11 run.",
         technique="For the parity machines, prove in Lean that sweep n writes row n of Pascal's triangle mod 2 in "
                   "4-cell letters. Lucas' theorem then gives every cell in closed form, and the halting condition "
                   "becomes a statement about binary digits that may be provable outright. The same template "
                   "(sweep = one CA step, then a closed form of the CA) is the route for the rest.",
         odds="medium for the parity pair, low for the others; untried, and a closed form is rare among holdouts."),
    dict(id="R06", name="Neighbours of DeepMind's PR 93 tables (the T3 and T4 engine)",
         sets=["1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF"],
         mechanism="Eleven open machines within one transition of the PR 93 tables, whose five decided members all "
                   "halt (PR 93, PR 100, PR 102, and our 1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA0RF_0LD--- and "
                   "1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LE). Behaviour varies: chaotic bells over runs 1^(6k+1), "
                   "sweeping transducers, counters with long digits.",
         known="`1RB1RA_1LC0RD_1LD1LB_1LE0LF_0RA---_0LB0LF` runs 10^1336 steps without a halt on the PR 93 engine, "
               "with a Coq skeleton that compiles and waits only for the engine to stop.",
         technique="Retarget the PR 93 run-length engine (each rule proved sound) to every member and run it to the "
                   "halt. It can prove halting only; a member that does not halt needs a different argument.",
         odds="medium: five of sixteen in this neighbourhood halted this way, but the remaining runs are already long."),
    dict(id="R07", name="Up/down counters and two binary counters with rebuilds",
         sets=["1RB1LD_1RC0RB_1LA1RC_1LE0LA_1LF---_1LC---", "1RB1LA_1LC1RD_1LA0LC_1RE0RB_1RB0RF_0RB---",
               "1RB1LE_1RC0RB_1RD1LF_1LA0LC_1LD0LA_---0RE", "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC",
               "1RB1LC_0RC0RB_1LD0LA_1LE---_1LF0LA_1LA0LB", "1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---",
               "1RB0RE_0RC0RF_1LD1RA_1RE0LD_0LB1RC_1LE---"],
         mechanism="One counter counts up while another counts down; when the down counter is empty a rebuild eats low "
                   "digits of the other and refills it. A halt needs one exact rebuild (for example a walk that "
                   "crosses the whole counter).",
         known="Ticks are proved in Lean for every size; the rebuilds are known in closed form (checked, not proved) "
               "and iterated past 10^150,000,000 steps. Two members have outside non-halting proofs: busycoq PR 57 "
               "(`1RB1LE_1RC0RB_1LD1RC_1LA1LE_1LF0LA_1LC---`) and PR 58 "
               "(`1RB1LC_0RC0RB_1LD0LA_1LE---_1LF1RA_1LA1LC`), neither compiled here.",
         technique="Compile PRs 57 and 58, then prove the closed rebuild recursions in Lean and extend the PR 57/58 wall "
                   "invariant to the case where a rebuild reads only part of the counter (that is where it failed "
                   "for the three siblings).",
         odds="medium: the rebuilds are already explicit maps; the last step is a number-theoretic inequality."),
    dict(id="R08", name="Reservoir counters: a chaotic zone eats a reservoir behind a growing block",
         sets=["1RB0RB_1LC1RA_1LF0LD_0LE1LD_1LA1LC_---1LA", "1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA0RF_---0RC",
               "1RB0RB_1RC1RA_0LD1LC_0RA1LE_1LF0LC_---1LA", "1RB1RD_1LC1RA_---1LD_1LE0RA_1LF0LE_0RB0LB",
               "1RB1LD_1RC0LE_1LA1RE_0LF1LA_1RB0RB_---0LB",
               "1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD"],
         mechanism="A block of words grows at one end; behind it a zone of about a hundred cells is rewritten like a "
                   "counter and slowly eats a reservoir; the far end is touched at rare events, and only those can halt.",
         known="Lean proves the halting pattern for the four 111110-machines; a model of their leftmost zone "
               "reproduces every real arrival at the left end. For `1RB1RC_1LC0RE_1LD0LB_1RA1LC_1RA1RF_---1RD` the "
               "reservoir is decoded as independent mod-4 counters and Lean proves a halt can only happen beyond the "
               "far end.",
         technique="Prove the leftmost-zone reduction in Lean (the 16 November plan's item 3), then model two zones "
                   "with the block between them. Could settle the four 111110-machines either way, and the same tools "
                   "apply to the five reservoir eaters.",
         odds="medium for the four, low for the rest (their next events are 2^1100 sweeps away or more)."),
    dict(id="R09", name="Word map phi with a counter: one table, a race between word and collisions",
         sets=["1RB1RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_1RA---"],
         mechanism="Six machines are one table with A1, F0 or the start changed (plus a separator counter one "
                   "transition away, `1RB---_1RC0RD_1RD1RA_1LE1RB_0LF0LE_1RF0RD`): a binary counter applies a word "
                   "map phi twice per step, and anomalies and collision cascades rewrite the word.",
         known="For `1RB0RF_1LC1RE_0LD0LC_1RD0RB_1RA0RB_0LC---` every macro step is proved in Lean as one map on "
               "word-and-counter configurations, and Lean proves the machine never halts if that map never fails; it "
               "does not fail in 10^8 macro steps.",
         technique="Port the one-map reduction to the five siblings (same table, so the rules carry over), then look "
                   "for an invariant of the map. A failure found by running the map would be a halting proof for all "
                   "members with the same run.",
         odds="medium-low: the race looks Collatz-like, but the reduction already exists."),
    dict(id="R10", name="Visit laws on streams (busycoq PR 59 family)",
         sets=["1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---", "1RB0LB_0RC0LD_1LD1RE_0LA0RF_1RB0RD_0RB---",
               "1RB0LB_0RC0LF_1LD1RE_0LA0RB_0RD0RF_0LA---", "1RB1LD_0RC0LF_1LD1RE_0LA0RB_0RD1RB_0LD---",
               "1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---"],
         mechanism="Two binary counters off one engine, read as a rewriting system on streams; the first four rules "
                   "are those of the PR 59 machines.",
         known="Busycoq PR 59 claims halting for `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD0LC_0RC---`, "
               "`1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RB_0RC---` and `1RB0LB_0RC0LD_1LD1RE_0LA0RF_0RD1RF_0RC---`, and "
               "PR 55 non-halting for `1RB0LB_0RC0LD_1LD1RE_0LA0RB_0RD1RF_1LA---`; none compiled here. The three "
               "open members rewrite 1011 differently and run past round 200,000 (visit law in Lean).",
         technique="Compile PRs 55 and 59 (four machines). For the three open members, continue the accelerated "
                   "visit-law run: our two halting proofs from 13 November came from this law.",
         odds="high for the four pending, low to medium for the three open."),
    dict(id="R11", name="Nested ternary counters (draining odometers)",
         pattern=(r"ternary|base-3 countdown", "Skelet"),
         mechanism="Segments of 111-blocks (or digits between blocks) drained by 3^j per event; segments run out one "
                   "after another and the counter settles into a new regime.",
         known="Every rule of `1RB0RF_1LC1RF_1RA0LD_0LC0RE_1LD---_0RC0RD` and `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` "
               "is proved in Lean; `1RB1RF_1LC0RE_1RD0LC_0LB0RA_1LD1RD_1RB---` passes round 33,199,619 without a "
               "halt, its next event about 2.7·10^12 rounds out.",
         technique="Exact macro simulators to the first top-level overflow (halt hunting), as for R04.",
         odds="medium for halts."),
    dict(id="R12", name="Two-word sweepers: base-3 and binary counters side by side",
         sets=["1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RE_0LC---", "1RB0LE_1LC0RE_0RA0LD_1LA1LF_0LC0RA_0LB---",
               "1RB---_1LC0RF_0RA0LD_1LE1LA_1RF0LF_0LC0RA", "1RB0LE_1LC0RE_0RA0LD_1LA0LF_0LC0RA_0RE---",
               "1RB0LD_0LC0RE_1LA0RD_0RB0LF_1RC1LA_0RB---"],
         mechanism="A base-3 counter and binary counters fed by one engine; overflows shift the layout and pile junk "
                   "into an undecoded middle.",
         known="The counters are proved in Lean for every size; DeepMind's file classes most of them as cryptids.",
         technique="Decode the middle first; no multi-machine proof is in sight.",
         odds="low."),
    dict(id="R13", name="Shifted-run quartet (F09)",
         sets=["1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---"],
         mechanism="Four tables one transition apart whose runs are one shifted run (observed to 2·10^12 steps): an "
                   "exact ternary counter whose digits are pairs of long alternating runs read mod 4.",
         known="The increment and the shuttle are proved in Lean for `1RB0RA_1LC0RE_0LD0LB_1LA1LF_1RA0LF_1LC---`; "
               "`1RB1RF_1LC0LB_1RE0LD_1LB0RF_0RA0RC_1RE---` has its own folder (`bb6-1RB1RF_1LC0LB`).",
         technique="A transfer theory for the shifted run would settle the four at once.",
         odds="medium-low."),
    dict(id="R14", name="Block lists rewritten like a cellular automaton (blocks of 4k+3 ones)",
         sets=["1RB---_0RC0LA_1LD0RB_1LE1LD_1LF0LC_1LB1RE"],
         mechanism="Bouncers whose tape is a list of numbers written as blocks of 4k+3 ones (or a dense and a sparse "
                   "form), rewritten chaotically on every round trip.",
         known="Halting patterns only.",
         technique="None yet; park unless R05 finds a usable closed form.",
         odds="low."),
]

COLLATZ = dict(
    id="R15", name="Collatz-like maps and cryptids (parked)",
    mechanism="The run is (provably, for many) the orbit of an explicit Collatz-like map: 3/2 and 4/3 growth with a "
              "parity- or residue-driven counter (Antihydra-like), doubling maps modulo a growing number, Euclid-like "
              "two-counter games, halving cascades.",
    known="Lean proves `halts_iff` for an explicit map for many of them (the index's 'proved map' column); DeepMind's "
          "file has a map or a cryptid label for most.",
    technique="No proof technique applies: these are open number-theory questions. Only halting can be decided, by "
              "running the proved maps far with big integers when the map is 'probviously halting'.",
    odds="very low for non-halting; occasional halts.")

PENDING = dict(
    id="R00", name="Outside proofs awaiting compilation (busycoq PRs 43 to 68)",
    technique="Compile each pull request on busycoq's BB6 branch with Print Assumptions appended, as was done for "
              "PRs 78 to 109 (`holdouts/external.json`), and record it. No research, and it can move every one of "
              "these machines from 'awaiting review' to decided here.")

# One line per family for the ranking table.
SHORT = {
    "R01": "one drift invariant on the shared core (same-run step done: 40 machines, 23 questions)",
    "R02": "automaton invariant for the word map P alone, plus the clock lemma in Lean",
    "R03": "shared Lean library for the core, then exact block-list runs to hunt halts",
    "R04": "halt hunting with exact odometer jumps (PR 83 / 89 method)",
    "R05": "prove each sweep is one CA step; closed form by Lucas' theorem for the parity pair",
    "R06": "retarget the PR 93 engine and run to the halt (halting only)",
    "R07": "compile PRs 57 and 58; prove the closed rebuild maps; extend the wall invariant",
    "R08": "Lean leftmost-zone reduction, then a two-zone model",
    "R09": "port the one-map reduction to the siblings; invariant of the map",
    "R10": "compile PRs 55 and 59; accelerated visit-law runs for the rest",
    "R11": "exact macro simulators to the first top-level overflow",
    "R12": "decode the middle first",
    "R13": "transfer theory for the shifted run",
    "R14": "none yet",
}

# The 13 November families (F01 to F12) for every machine that was open then; from the project file plan/families.json.
OLD_FAMILY_NAMES = {
    "F01": "Periodic blocks driven by a bounded engine", "F02": "Clock-and-word and two-counter shift-overflow counters",
    "F03": "Binary counters with markers, epochs and resets", "F04": "Collatz-like bells with a tail, prefix or stack",
    "F05": "Nested block counter with a shared core table", "F06": "Other block-list countdown counters (Skelet 1-like)",
    "F07": "Chaotic bells over block lists", "F08": "Counter beside a chaotic edge or wall",
    "F09": "Bouncers over lists of counters", "F10": "Block-splitting 'mess' machines",
    "F11": "Defect gases, particle seas and cellular-automaton zones", "F12": "Cryptids and 'probviously' halting machines",
}


def load_old():
    p = os.path.join(HERE, "families_13nov.json")
    with open(p) as f:
        return json.load(f)


def main():
    with open(os.path.join(HERE, "triage.json")) as f:
        triage = json.load(f)
    with open(os.path.join(HERE, "known.json")) as f:
        known = {k: v for k, v in json.load(f).items() if not k.startswith("_")}
    spec_by = {s["machine"]: s for _, s in bp.specs()}
    rows = {r["m"]: r for r in bp.index_rows(triage, known, spec_by)}
    machines = sorted(rows)
    und = [m for m in machines if rows[m]["st"] in ("open", "cryptid", "pr")]
    old = load_old()
    D = distances(machines)
    tset = table_sets(machines, D)
    idx = {m: i for i, m in enumerate(machines)}
    desc = {m: (rows[m]["sum"] or "") + " " + (rows[m]["g"] or "") for m in machines}

    assigned = {}
    for fam in FAMILIES:
        mem = set()
        for s in fam.get("sets", []):
            mem |= {m for m in und if tset[m] == tset[s]}
        if "pattern" in fam:
            pat, cls = fam["pattern"]
            mem |= {m for m in und if re.search(pat, desc[m], re.I) and re.search(cls, rows[m]["tc"])}
        for o in fam.get("old", []):
            mem |= {m for m in und if old.get(m) == o}
        assert all(m in und for m in fam.get("extra", [])), fam["id"]
        mem |= set(fam.get("extra", []))
        mem -= set(fam.get("drop", []))
        for m in sorted(mem):
            if m in assigned:
                raise SystemExit(f"{m} in {assigned[m]} and {fam['id']}")
            assigned[m] = fam["id"]
    for m in und:
        if m in assigned:
            continue
        e = rows[m]
        if old.get(m) in ("F12", "F04") or e["st"] == "cryptid" or e["cr"] or (e["dm"] and e["dm"]["k"] in ("cryptid", "map")):
            assigned[m] = COLLATZ["id"]
        elif e["st"] == "pr":
            assigned[m] = PENDING["id"]
        else:
            assigned[m] = old[m]  # residual: the 13 November family

    pending = sorted(m for m in und if rows[m]["st"] == "pr")
    by = collections.defaultdict(list)
    for m, f in assigned.items():
        by[f].append(m)

    sizes = collections.Counter(tset[m] for m in machines)
    label = {s: f"T{i}" for i, s in enumerate(sorted(sizes, key=lambda s: (-sizes[s], s)), 1)}

    def mrow(m):
        e = rows[m]
        return {"m": m, "id": e["id"], "st": e["st"], "tc": e["tc"], "old": old.get(m, ""), "set": label[tset[m]],
                "set_size": sizes[tset[m]], "folder": e["f"],
                "pr": [p[0] for p in e["pr"]], "map": bool(e["mp"]), "dm": e["dm"]["k"] if e["dm"] else ""}

    fams_out = []
    for rank, fam in enumerate(FAMILIES, 1):
        fams_out.append({k: fam[k] for k in ("id", "name", "mechanism", "known", "technique", "odds")} |
                        {"rank": rank, "short": SHORT[fam["id"]], "machines": [mrow(m) for m in sorted(by[fam["id"]])]})
    fams_out.append({k: COLLATZ[k] for k in ("id", "name", "mechanism", "known", "technique", "odds")} |
                    {"rank": None, "short": "halt hunts on proved maps only",
                     "machines": [mrow(m) for m in sorted(by[COLLATZ["id"]])]})
    elsewhere = collections.Counter(assigned[m] for m in pending if assigned[m] != PENDING["id"])
    short = (f"compile and record; listed here are the {len(by[PENDING['id']])} with no other family, the other "
             f"{sum(elsewhere.values())} pending machines sit in " + ", ".join(sorted(elsewhere)))
    fams_out.append({"id": PENDING["id"], "name": PENDING["name"], "mechanism": "Various; no other family.",
                     "known": "", "technique": PENDING["technique"], "odds": "high", "rank": 0, "short": short,
                     "machines": [mrow(m) for m in sorted(by[PENDING["id"]])]})
    residual = {f: {"id": f, "name": OLD_FAMILY_NAMES[f] + " (rest)", "machines": [mrow(m) for m in sorted(by[f])]}
                for f in sorted(OLD_FAMILY_NAMES) if by.get(f)}

    out = {
        "_source": "holdouts/regroup.py, " + ASOF + ". Families of the undecided holdouts (standing open, cryptid or "
                   "pr on the index) that one proof technique could settle together; ranked R01 first. 'set' is the "
                   "table set (single-linkage at table distance <= 1 up to renaming and mirror; T1 is the largest, "
                   "and table_sets names each by its smallest member); 'old' is the 13 November family; 'pending' are the machines whose only proof is an "
                   "uncompiled outside pull request.",
        "asof": ASOF,
        "undecided": len(und),
        "families": fams_out,
        "residual": list(residual.values()),
        "pending": pending,
        "machine": {m: assigned[m] for m in sorted(assigned)},
        "table_sets": {label[s]: {"size": n, "named_by": s} for s, n in sorted(sizes.items(), key=lambda x: label[x[0]]) if n > 1},
        "distance_pairs": {str(d): int(c) for d, c in zip(*np.unique(D[np.triu_indices(len(machines), 1)],
                                                                     return_counts=True))},
    }
    with open(os.path.join(HERE, "families.json"), "w") as f:
        json.dump(out, f, indent=1, ensure_ascii=False)
        f.write("\n")
    write_md(out, rows)
    print(len(und), "undecided;", {f["id"]: len(f["machines"]) for f in fams_out},
          {r["id"]: len(r["machines"]) for r in residual.values()})


STAND = {"open": "open", "cryptid": "cryptid", "pr": "awaiting review"}


def write_md(out, rows):
    L = []
    w = L.append
    w("# Families of the undecided holdouts (" + ASOF + ")")
    w("")
    w(f"Of the 608 holdouts, **{out['undecided']}** are undecided here: open, cryptid, or covered only by an outside "
      f"proof that has not been compiled here ({len(out['pending'])} machines). This note regroups them into families "
      "where one proof technique could settle several machines at once, and ranks the families. It replaces the "
      "ranking of the 13 November plan (F01 to F12, kept in `families.json` as each machine's `old` family). The "
      "machine-readable version is [`families.json`](families.json), written with this note by "
      "[`regroup.py`](regroup.py); the [holdout map](../pages/holdouts/index.html) can filter by family.")
    w("")
    w("## How the families were made")
    w("")
    w("- **Table distance.** For every pair of the 608 machines, `regroup.py` counts the transitions that differ "
      "between the two tables, minimised over the 720 renamings of the states and the mirror image. Distance 0 is the "
      "same table started elsewhere (" + str(out["distance_pairs"].get("0", 0)) + " pairs), distance 1 one changed "
      "transition (" + str(out["distance_pairs"].get("1", 0)) + " pairs). Joining machines at distance 1 or less "
      "gives the *table sets*. Machines in one table set share most of their macro rules, so a Lean library written "
      "for one usually proves on the others (as `Family.lean` did for all 40 of F05).")
    w("- **Mechanism.** Table sets with the same mechanism, read from each machine's own description and the "
      "community tracker's class, were joined into one family, and machines with the same mechanism on unrelated "
      "tables were added by a pattern on their descriptions (the rules are in `regroup.py`).")
    w("- **Ranking.** By the number of machines one argument would settle, weighed by how likely the argument is to "
      "work, judged from what is already proved. These are judgements, not results.")
    w("- Machines that fit none of the families keep their 13 November family (listed at the end), and Collatz-like "
      "machines and cryptids form one parked family.")
    w("")
    w("## Ranking")
    w("")
    w("| rank | family | machines | of which awaiting review | technique | odds |")
    w("|---|---|---|---|---|---|")
    fams = out["families"]
    pend = [f for f in fams if f["id"] == "R00"][0]
    w(f"| 0 | **{pend['id']}** {pend['name']} | {len(out['pending'])} (all) | {len(out['pending'])} | "
      "compile and record | high |")
    for f in fams:
        if f["id"] in ("R00", "R15"):
            continue
        npr = sum(1 for m in f["machines"] if m["st"] == "pr")
        w(f"| {f['rank']} | **{f['id']}** {f['name']} | {len(f['machines'])} | {npr or ''} | "
          f"{SHORT[f['id']]} | {f['odds'].split(':')[0].split(';')[0].split(' (')[0].rstrip('.')} |")
    c = [f for f in fams if f["id"] == "R15"][0]
    w(f"| parked | **{c['id']}** {c['name']} | {len(c['machines'])} | "
      f"{sum(1 for m in c['machines'] if m['st'] == 'pr') or ''} | halt hunts on proved maps only | very low |")
    nres = sum(len(r["machines"]) for r in out["residual"])
    w(f"| - | the rest of F01 to F11 | {nres} | | no shared technique found | |")
    w("")
    w("## Recommended next attacks")
    w("")
    w(f"1. **Compile the outside proofs of busycoq PRs 43 to 68** ({len(out['pending'])} machines). They are the only "
      "machines on the list whose proofs exist but have not been checked here, and checking them is mechanical "
      "(the same procedure as for PRs 78 to 109). Ten of them also belong to families below (R04, R07, R10 and R15).")
    n = {f["id"]: len(f["machines"]) for f in fams}
    w(f"2. **R01, the F05 core** ({n['R01']} machines). The largest family by far, with its whole macro structure already "
      "proved in Lean on all 40 core tables. One invariant on the drift settles all of them. The equivalence step is "
      "done (the 40 are 23 questions); the invariant itself looks like a Collatz-type statement, so the odds are low.")
    w(f"3. **R02, clock and word** ({n['R02']} machines on six tables). The clock lemma is in Lean for six; what is left is "
      "a finite-state question about one word map per machine, which an automaton search on the word alone "
      "can answer far more cheaply than the whole-tape search that failed.")
    w(f"4. **R04 and R11, base-4 and ternary countdown counters** ({n['R04'] + n['R11']} machines). Halt hunting with exact odometer "
      "jumps; this kind of family (F06) produced half of the decisions of the week of 13 November, all halting, and short-timer tapes of the "
      "same shape are proved to halt.")
    w(f"5. **R05, cellular-automaton sweeps** ({n['R05']} machines). New idea: for the two running-parity machines, a Lean "
      "proof that each sweep is one row of Pascal's triangle mod 2 turns halting into a statement about binary "
      "digits (Lucas' theorem).")
    w("")
    w("Next in line: R03 (one table core, a shared library as for F05) and R06 (the PR 93 engine retargeted). "
      "R07 and R10 start with the compiles in step 1.")
    w("")
    w("## The families")
    for f in fams:
        if f["id"] == "R00":
            continue
        w("")
        w(f"### {f['id']}. {f['name']} ({len(f['machines'])} machines)")
        w("")
        w(f"**Mechanism.** {f['mechanism']}")
        w("")
        if f["known"]:
            w(f"**Known.** {f['known']}")
            w("")
        w(f"**Technique.** {f['technique']}")
        w("")
        w(f"**Odds.** {f['odds']}")
        w("")
        w(table(f["machines"]))
    w("")
    w(f"### R00. {pend['name']} ({len(out['pending'])} machines)")
    w("")
    w(pend["technique"] + " Machines here that also belong to a family above are listed there too.")
    w("")
    w(table([m for f in fams for m in f["machines"] if m["st"] == "pr"]))
    w("")
    w("## The rest, by their 13 November family")
    w("")
    w("No technique shared by several of these is in sight; they are listed so that every undecided machine has a "
      "place.")
    for r in out["residual"]:
        w("")
        w(f"### {r['id']} {r['name']} ({len(r['machines'])} machines)")
        w("")
        w(table(r["machines"]))
    w("")
    with open(os.path.join(HERE, "FAMILIES.md"), "w") as f:
        f.write("\n".join(L))


def table(ms):
    L = ["| machine | standing | community class | table set | 13 Nov family | notes |", "|---|---|---|---|---|---|"]
    for m in sorted(ms, key=lambda x: (int(x["set"][1:]), x["m"])):
        notes = []
        if m["pr"]:
            notes.append("busycoq PR " + ", ".join(map(str, m["pr"])))
        if m["map"]:
            notes.append("halts-iff map in Lean")
        if m["dm"]:
            notes.append("DeepMind: " + m["dm"])
        same = f"{m['set']} ({m['set_size']})" if m["set_size"] > 1 else "-"
        link = m["folder"][len("holdouts/"):] if m["folder"].startswith("holdouts/") else "../" + m["folder"]
        L.append(f"| [`{m['m']}`]({link}/README.md) | {STAND[m['st']]} | {m['tc']} | {same} | {m['old'] or '-'} | "
                 f"{'; '.join(notes)} |")
    return "\n".join(L)


if __name__ == "__main__":
    main()
