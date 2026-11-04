"""A linear cycle accelerator for the macro simulator (`bbtools.macro`): many cycles of a regular regime at once.

A run often enters a regime where its run-length tape, at successive *sample points* (say each time the head reaches
the end of the tape in a given state), keeps the same words in the same order and only some counts move, each by a
constant per cycle: a block grows by 2, a wall shrinks by 2, and the steps per cycle grow by a constant.  This module

1. *detects* such a regime from 2 or 3 samples with the same shape (`detect`);
2. *proves* the one-cycle rule with `bbtools.symtm`: every changing count (and every long count) becomes a variable
   `n_i` (plus a small offset, so a few copies can be unrolled), the short unchanging runs stay concrete (as cells),
   and `symtm.prove` runs the symbolic start configuration to the end configuration, the counts moved by their
   increments, and writes a Lean theorem for all values of the variables (`prove_cycle`, a `Rule`).  Repeats are
   re-bracketed next to the head where that lets a shift rule cross them (`symtm.try_rotate`), so a run the macro
   machine crosses in one step is crossed in the proof too.  The cycle is proved from the second-last sample and
   its proved step count must equal the sampled one;
3. *applies* k cycles at once (`Rule.apply`): the counts move by k times their increments and the step count by the
   exact sum  k*S + D*k*(k-1)/2  (S the steps of the first cycle, D the increment of the steps per cycle, both read
   off the proved step count, which is linear in the variables), with k chosen so that every shrinking count stays at
   least `margin` above what the rule needs;
4. `Accelerator` drives a `MacroRun` with all of this, for any machine.

Trust: the rule is a theorem (Lean is the judge: compile `Accelerator.lean_file()` after the machine's definition
from `bbtools.leangen`), and the jump is k applications of it, valid since every variable stays >= 0 throughout (an
induction on k that is not written out in Lean).  Two things are not part of the theorem and are
extrapolated from the samples: the absolute head position `pos` (the machine cannot see it) and the counts of runs of
the blank word next to the blank ends of the tape (which are blank tape, so dropped from the symbolic tape).
tools/tests/test_tools.py checks jumps against plain macro runs, stacks, position and step count.

Use: `Accelerator(MacroRun(machine, k)).run(steps)`, or call `snapshot`, `detect`, `prove_cycle` and `Rule.apply`
from your own loop with your own sample points.  The block size matters: a run is crossed in the proof only if the
macro machine crosses it, so pick k as for the macro machine (4 for 1RB1RF_1LC0LB, where 2 leaves some walls to be
eaten block by block).

usage: python3 -m bbtools.cycles MACHINE K STEPS     run with the accelerator, printing each jump
"""
import sys
from dataclasses import dataclass, field

from . import symtm
from .macro import MacroRun
from .machine import STATES

CONCRETE_MAX = 24       # an unchanging run at most this long stays a concrete count in the symbolic tape
OFFSETS = (1, 3, 8)     # tried in turn: the constant part of each variable count (beyond the shrink per cycle)
MAX_SEG = 40            # single steps per `rfl` in the Lean proofs
HIST_KEYS = 64          # the samples of this many shapes are kept
MAX_ERRORS = 100


# ---------------------------------------------------------------- samples
@dataclass(frozen=True)
class Snap:
    """A macro configuration: stacks as tuples of (word, count) from the blank end towards the head."""
    steps: int
    pos: int
    state: int
    dir: int
    left: tuple
    right: tuple

    def key(self):
        return (self.state, self.dir, tuple(w for w, _ in self.left), tuple(w for w, _ in self.right))

    def counts(self):
        return tuple(c for _, c in self.left) + tuple(c for _, c in self.right)


def snapshot(run):
    return Snap(run.steps, run.pos, run.state, run.dir,
                tuple((x, c) for x, c in run.left[1:]), tuple((x, c) for x, c in run.right[1:]))


def at_tape_end(run):
    """The default sample predicate: the head faces blank tape (it stands at one end of the written tape)."""
    front = run.right if run.dir == 1 else run.left
    return len(front) == 1


@dataclass(frozen=True)
class Cycle:
    """A candidate regime: the count increments per cycle (left runs, then right runs) seen in the samples."""
    key: tuple
    delta: tuple
    dpos: int
    dsteps: tuple       # the steps of each sampled cycle


def detect(snaps):
    """A Cycle if the 2 or 3 snapshots (in run order) have one shape and counts moving by constant increments, else None."""
    if len(snaps) < 2 or any(s.key() != snaps[0].key() for s in snaps):
        return None
    cs = [s.counts() for s in snaps]
    delta = tuple(b - a for a, b in zip(cs[0], cs[1]))
    if not any(delta):
        return None
    dpos = snaps[1].pos - snaps[0].pos
    for s, t in zip(snaps[1:], snaps[2:]):
        if tuple(b - a for a, b in zip(s.counts(), t.counts())) != delta or t.pos - s.pos != dpos:
            return None
    return Cycle(snaps[0].key(), delta, dpos, tuple(t.steps - s.steps for s, t in zip(snaps, snaps[1:])))


# ---------------------------------------------------------------- the rule
def _blank_word(w):
    return not any(w)


@dataclass
class Rule:
    """A proved one-cycle rule.  `spec[i]` for run i (left runs, then right runs) is ('var', name, offset),
    ('const', count) or ('blank',) (a blank-word run next to a blank end, not in the symbolic tape)."""
    key: tuple
    delta: tuple
    dpos: int
    spec: list
    steps: symtm.Lin                # steps of one cycle, linear in the variables
    lean: str
    name: str
    start: symtm.Config = field(repr=False, default=None)     # the symbolic configurations of the theorem
    end: symtm.Config = field(repr=False, default=None)

    def __post_init__(self):
        self._index = {sp[1]: i for i, sp in enumerate(self.spec) if sp[0] == "var"}

    def env(self, snap):
        """Values of the variables at `snap`, or None if the rule does not apply there."""
        if snap.key() != self.key:
            return None
        env = {}
        for sp, c in zip(self.spec, snap.counts()):
            if sp[0] == "var":
                if c < sp[2]:
                    return None
                env[sp[1]] = c - sp[2]
            elif sp[0] == "const" and c != sp[1]:
                return None
        return env

    def cycle_steps(self, env):
        """(S, D): the first cycle from `env` takes S steps, and each later one D more."""
        S = self.steps.subs(env)
        D = sum(a * self.delta[self._index[v]] for v, a in self.steps.c.items())
        return S, D

    def max_cycles(self, snap, margin=0):
        """The most cycles that can be applied from `snap` with every variable still >= margin after them (so >= 0 at
        each cycle's start, as the rule needs).  None if nothing shrinks."""
        env = self.env(snap)
        if env is None:
            return 0
        k = None
        for sp, d in zip(self.spec, self.delta):
            if sp[0] == "var" and d < 0:
                room = env[sp[1]] - margin
                if room < 0:
                    return 0
                kk = room // (-d)
                k = kk if k is None else min(k, kk)
        return k        # None: nothing shrinks, any number of cycles

    @staticmethod
    def total_steps(S, D, k):
        return k * S + D * k * (k - 1) // 2

    def apply(self, run, k):
        """k cycles at once on a MacroRun standing at a sample point this rule applies to.  Returns the steps added."""
        snap = snapshot(run)
        env = self.env(snap)
        if env is None:
            raise ValueError("the rule does not apply here")
        mk = self.max_cycles(snap)
        if mk is not None and k > mk:
            raise ValueError(f"{k} cycles would take a count below what the rule needs (at most {mk})")
        S, D = self.cycle_steps(env)
        n = self.total_steps(S, D, k)
        nl = len(snap.left)
        for i, d in enumerate(self.delta):
            if d:
                ent = run.left[1 + i] if i < nl else run.right[1 + i - nl]
                ent[1] += k * d
        run.steps += n
        run.pos += k * self.dpos
        return n


def _sym_config(snap, spec, shift):
    """The symbolic tape of `snap` per `spec`, each variable count moved by shift[i]."""
    nl = len(snap.left)
    toks = []
    for i, ((w, c), sp) in enumerate(zip(snap.left + snap.right, spec)):
        if sp[0] == "blank":
            toks.append([])
        elif sp[0] == "const":          # as cells: a crossing lemma at a numeral count is slow in Lean
            toks.append(list(w) * c)
        else:
            toks.append([symtm.Rep(w, symtm.Lin(sp[1]) + (sp[2] + shift[i]))])
    left = [symtm.Blank()] + [t for ts in toks[:nl] for t in ts]
    right = [t for ts in reversed(toks[nl:]) for t in ts] + [symtm.Blank()]
    if snap.dir == -1:              # the head reads the last cell of the block on its left
        top = left[-1]
        if isinstance(top, symtm.Blank):
            right.insert(0, 0)
        elif isinstance(top, int):
            right.insert(0, left.pop())
        else:
            left[-1:] = ([symtm.Rep(top.word, top.n - 1)] if not (top.n - 1).is_zero() else []) + list(top.word[:-1])
            right.insert(0, top.word[-1])
    return symtm.Config(left, snap.state, right)


def _spec(snap, delta, base):
    runs = snap.left + snap.right
    nl = len(snap.left)
    spec = []
    for i, ((w, c), d) in enumerate(zip(runs, delta)):
        edge = i == 0 or i == nl     # next to the blank end of its side
        if edge and _blank_word(w):
            spec.append(("blank",))
        elif d == 0 and c <= CONCRETE_MAX:
            spec.append(("const", c))
        else:
            o = base + max(0, -d)
            if c < o:
                return None
            spec.append(("var", f"n{i}", o))
    return spec


class CycleProofError(Exception):
    """`small`: some offsets were not tried because a count was too small for them (larger counts may succeed)."""
    def __init__(self, msg, small=False):
        super().__init__(msg)
        self.small = small


def prove_cycle(machine, snap, cycle, name="cycle", offsets=OFFSETS):
    """Prove the one-cycle rule of `cycle` from `snap` (a sample of it).  Returns a Rule, or raises CycleProofError."""
    m = symtm.Machine.parse(machine) if isinstance(machine, str) else machine
    errors, small = [], False
    for base in offsets:
        spec = _spec(snap, cycle.delta, base)
        if spec is None:
            small = True
            continue
        start = _sym_config(snap, spec, [0] * len(spec))
        end = _sym_config(snap, spec, list(cycle.delta))
        try:
            lean, fin = symtm.prove(m, name, start, end,
                                    doc=f"one cycle: {_describe(snap, spec, cycle.delta)}", rotate=True,
                                    count_first=True, max_seg=MAX_SEG)
        except (symtm.ProofError, ValueError) as e:
            errors.append(str(e))
            continue
        rule = Rule(cycle.key, cycle.delta, cycle.dpos, spec, fin.steps, lean, name, start, end)
        env = rule.env(snap)
        if env is None or rule.steps.subs(env) != cycle.dsteps[0]:
            errors.append(f"the proved cycle takes {rule.steps} steps, not the sampled {cycle.dsteps[0]}")
            continue
        return rule
    raise CycleProofError("; ".join(errors) or "no variables fit the counts", small)


def _describe(snap, spec, delta):
    parts = []
    for (w, c), sp, d in zip(snap.left + snap.right, spec, delta):
        if sp[0] == "var" and d:
            parts.append(f"({''.join(map(str, w))})^{sp[1]} {'+' if d > 0 else '-'}{abs(d)}")
    return ", ".join(parts) + f", state {STATES[snap.state]}"


# ---------------------------------------------------------------- the driver
class Accelerator:
    """Runs a MacroRun, applying proved cycle rules at sample points.

    sample(run) -> bool chooses the sample points (default: the head faces blank tape).  `samples` (2 or 3) is how
    many consecutive samples of one shape must agree before a proof is tried; `margin` is how far above what the rule
    needs each shrinking count is kept; `min_cycles` is the least jump worth making."""

    def __init__(self, run, sample=at_tape_end, samples=3, margin=2, min_cycles=2):
        self.run_ = run
        self.sample = sample
        self.samples = samples
        self.margin = margin
        self.min_cycles = min_cycles
        self.hist = {}          # shape -> its last 3 samples, for the HIST_KEYS shapes sampled last
        self.rules = []         # proved rules, in the order found
        self.by_key = {}        # shape -> its rules
        self.failed = set()     # cycles that could not be proved
        self.small = set()      # ... with counts too small for some offsets: tried again once they are large enough
        self.errors = []        # (sample, cycle, why) of the last MAX_ERRORS cycles that could not be proved
        self.jumps = []         # (steps before, cycles, steps after, rule name)

    @property
    def m(self):
        return self.run_.m

    def _rule_for(self, snap):
        h = self.hist.get(snap.key(), [])
        for rule in self.by_key.get(snap.key(), ()):
            if rule.env(snap) is not None and len(h) >= 2:
                cyc = detect(h[-2:])
                if cyc and cyc.delta == rule.delta:
                    return rule
        if len(h) < self.samples:
            return None
        cyc = detect(h[-self.samples:])
        if cyc is None:
            return None
        sig = (cyc.key, cyc.delta, tuple(c for c, d in zip(h[-1].counts(), cyc.delta) if d == 0 and c <= CONCRETE_MAX))
        if sig in self.failed or (sig in self.small and _spec(h[-2], cyc.delta, max(OFFSETS)) is None):
            return None
        try:
            rule = prove_cycle(self.m, h[-2], Cycle(cyc.key, cyc.delta, cyc.dpos, (cyc.dsteps[-1],)),
                               name=f"cycle{len(self.rules)}")
        except CycleProofError as e:
            (self.small if e.small else self.failed).add(sig)
            self.errors.append((h[-1], cyc, str(e)))
            del self.errors[:-MAX_ERRORS]
            return None
        self.rules.append(rule)
        self.by_key.setdefault(rule.key, []).append(rule)
        return rule

    def jump(self, limit=None):
        """At a sample point: jump as far as a rule allows (without passing `limit` steps).  Returns cycles done."""
        r = self.run_
        snap = snapshot(r)
        rule = self._rule_for(snap)
        if rule is None:
            return 0
        env = rule.env(snap)
        if env is None:
            return 0
        k = rule.max_cycles(snap, self.margin)
        S, D = rule.cycle_steps(env)
        if limit is not None:
            lo, hi = 0, k if k is not None else 1
            while k is None and rule.total_steps(S, D, hi) + r.steps <= limit:
                hi *= 2
            while lo < hi:                  # the most cycles that stay within the limit
                mid = (lo + hi + 1) // 2
                if r.steps + rule.total_steps(S, D, mid) <= limit:
                    lo = mid
                else:
                    hi = mid - 1
            k = lo
        if k is None or k < self.min_cycles:
            return 0
        before = r.steps
        rule.apply(r, k)
        self.jumps.append((before, k, r.steps, rule.name))
        self.hist[snap.key()] = [snapshot(r)]
        return k

    def run(self, steps):
        """Macro steps and jumps until at least `steps` machine steps have run (or the machine halts)."""
        r = self.run_
        while r.steps < steps:
            if not r.step():
                break
            if self.sample(r):
                s = snapshot(r)
                h = self.hist.pop(s.key(), [])
                self.hist[s.key()] = h          # most recent last
                if len(self.hist) > HIST_KEYS:
                    del self.hist[next(iter(self.hist))]
                h.append(s)
                del h[:-3]
                self.jump(limit=steps)
        return self

    def lean_file(self, machine_module, ns, doc="Cycle rules proved by bbtools.cycles"):
        return symtm.rules_file(machine_module, ns, [rule.lean for rule in self.rules], doc)


def main(argv):
    if len(argv) != 3:
        sys.exit(__doc__)
    machine, k, steps = argv[0], int(argv[1]), int(float(argv[2]))
    a = Accelerator(MacroRun(machine, k)).run(steps)
    for before, n, after, name in a.jumps:
        print(f"{before:.4e} -> {after:.4e}  {n} cycles of {name}")
    r = a.run_
    print(f"{'halted after' if r.halted else 'at'} {r.steps} steps, {len(a.rules)} rules, {len(a.jumps)} jumps")
    s = str(r)
    print(s if len(s) < 2000 else s[:2000] + " ...")


if __name__ == "__main__":
    main(sys.argv[1:])
