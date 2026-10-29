"""Turing machines in the standard text format, and a plain reference simulator.

The format is the one bbchallenge.org uses: one group per state, separated by `_`, each group holding the
transition on 0 and the transition on 1 as three characters: the symbol written, the direction (`L` or `R`) and the
next state (`A`, `B`, ...).  A transition is a halt if it is `---` or if its next state is not one of the machine's
states (`1RZ`, `1RH`).  Only two symbols are supported.

Step counts follow the bbchallenge convention: the halting transition counts as a step.  So a machine "halts after
t steps" when t - 1 ordinary transitions are followed by a halting one (BB(5)'s champion: 47,176,870).
"""

from dataclasses import dataclass

STATES = "ABCDEFGHIJ"


@dataclass(frozen=True)
class Machine:
    text: str
    n: int                      # number of states
    table: tuple                # table[s][y] = (write, move, next) or None (halt); move is +1 (R) or -1 (L)

    @staticmethod
    def parse(text):
        groups = text.strip().split("_")
        n = len(groups)
        if not 1 <= n <= len(STATES):
            raise ValueError(f"bad number of states: {n}")
        table = []
        for g in groups:
            if len(g) != 6:
                raise ValueError(f"bad group {g!r} in {text!r}")
            row = []
            for y in (0, 1):
                t = g[3 * y:3 * y + 3]
                if t == "---" or t[2] not in STATES[:n]:
                    row.append(None)
                    continue
                if t[0] not in "01" or t[1] not in "LR":
                    raise ValueError(f"bad transition {t!r} in {text!r}")
                row.append((int(t[0]), 1 if t[1] == "R" else -1, STATES.index(t[2])))
            table.append(tuple(row))
        return Machine(text.strip(), n, tuple(table))

    def halting_transitions(self):
        """The (state, symbol) pairs with no transition, as strings like 'D0'."""
        return [f"{STATES[s]}{y}" for s in range(self.n) for y in (0, 1) if self.table[s][y] is None]

    def __str__(self):
        return self.text


def state_name(s):
    return STATES[s]


class Tape:
    """A two-way infinite binary tape in a bytearray that grows on demand."""

    def __init__(self, size=1024):
        self.cells = bytearray(size)
        self.off = size // 2        # index of position 0
        self.lo = self.hi = 0       # the leftmost and rightmost positions the head has visited

    def _grow(self, pos):
        n = len(self.cells)
        new = bytearray(3 * n)
        new[n:2 * n] = self.cells
        self.cells = new
        self.off += n

    def get(self, pos):
        i = pos + self.off
        if i < 0 or i >= len(self.cells):
            return 0
        return self.cells[i]

    def set(self, pos, v):
        i = pos + self.off
        while i < 0 or i >= len(self.cells):
            self._grow(pos)
            i = pos + self.off
        self.cells[i] = v

    def word(self, lo=None, hi=None):
        lo = self.lo if lo is None else lo
        hi = self.hi if hi is None else hi
        return [self.get(p) for p in range(lo, hi + 1)]


class Run:
    """A machine run on a concrete tape: `step()` makes one transition."""

    def __init__(self, machine, state=0, tape=None, head=0):
        self.m = machine
        self.state = state
        self.tape = tape or Tape()
        self.head = head
        self.steps = 0
        self.halted = False

    def step(self):
        if self.halted:
            raise RuntimeError("the machine has halted")
        y = self.tape.get(self.head)
        tr = self.m.table[self.state][y]
        self.steps += 1
        if tr is None:
            self.halted = True
            return False
        w, d, s = tr
        self.tape.set(self.head, w)
        self.head += d
        self.state = s
        if self.head < self.tape.lo:
            self.tape.lo = self.head
        if self.head > self.tape.hi:
            self.tape.hi = self.head
        return True

    def run(self, max_steps):
        """Run until a halt or until `steps` reaches max_steps. Returns True if halted."""
        while self.steps < max_steps:
            if not self.step():
                return True
        return False

    def ones(self):
        return sum(self.tape.word())

    def config_str(self, lo=None, hi=None, rle=True):
        lo = self.tape.lo if lo is None else min(lo, self.head)
        hi = self.tape.hi if hi is None else max(hi, self.head)
        return format_config(self.tape.word(lo, hi), self.head - lo, STATES[self.state], rle=rle)


def rle_cells(cells):
    """Run-length tokens of a list of cells: '1^5 0 1^2'."""
    out = []
    i = 0
    while i < len(cells):
        j = i
        while j < len(cells) and cells[j] == cells[i]:
            j += 1
        out.append(f"{cells[i]}^{j - i}" if j - i > 1 else str(cells[i]))
        i = j
    return out


def format_config(cells, head_index, state, rle=True):
    """`left S>x right`: the head in state S reading cell x."""
    left, here, right = cells[:head_index], cells[head_index], cells[head_index + 1:]
    fmt = rle_cells if rle else (lambda cs: [str(c) for c in cs])
    return " ".join(fmt(left) + [f"{state}>{here}"] + fmt(right))


def records(machine, max_steps, state=0):
    """Yield (steps, side, run) each time the head reaches a cell no earlier step has reached.
    `side` is 'L' or 'R'. The run is the live object: read it before advancing the generator."""
    r = Run(machine, state)
    while r.steps < max_steps:
        lo, hi = r.tape.lo, r.tape.hi
        if not r.step():
            return
        if r.tape.lo < lo:
            yield r.steps, "L", r
        elif r.tape.hi > hi:
            yield r.steps, "R", r


def run_blank(text, max_steps):
    """(halted, steps, ones) of the run from blank tape, at most max_steps steps."""
    r = Run(Machine.parse(text))
    h = r.run(max_steps)
    return h, r.steps, r.ones()
