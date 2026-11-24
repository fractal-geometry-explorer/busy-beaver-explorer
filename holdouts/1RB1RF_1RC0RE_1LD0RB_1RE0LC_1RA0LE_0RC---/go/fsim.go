// fsim.go: exact accelerated simulator for 1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC--- (block queue with cursors).
// The rope engine and macro rules of py/qsim.py, ported to Go with math/big integers, plus
//   - bulk feeding: when two visits of the right end show the feeding rule (cursor one a further left and flipped,
//     the block right of it +4 or +2, the end block -2), all the visits until the block or the end block runs out
//     are applied at once, with their exact step count (a sum of an arithmetic progression);
//   - periodic jumps: when the shape of the tape (the counts abstracted when large) recurs with a period p and the
//     same change of the counts twice, J periods are applied at once (the decreasing counts are kept above the
//     shape thresholds) and the period after the jump must reproduce shapes, changes and step count, otherwise the
//     jump is rolled back and halved.  The jumps are validated this way, not proved.
//
// usage (go build -o fsim . in this folder):
//   fsim D quiet            run from blank tape until the step count has more than D digits; prints births of a
//                           cursor half way across a separator (BIRTH mid-hop), every visit with three cursor cells
//                           1 side by side (TRIPLE) and the end block at that visit (MARGIN), HALT if it halts
//   fsim D check0           plain rope engine against a cell-by-cell simulator of the table, at every visit
//   fsim D check1           bulk feeding against the plain rope engine, at every visit of the faster one
//   fsim D check2           bulk feeding with jumps against bulk feeding alone
//   fsim D quiet cf         the same, and at each triple also the counterfactual of cf.go: the tape as it would be had
//                           the end block run out at that visit (a birth leaving the triple standing), run until the
//                           first cursor reaches the triple (CF ... HALT, or destroyed)
//   fsim D dump=F,LO,HI     write "steps hash-of-tape" for the visits with 10^LO <= steps < 10^HI (compare runs
//                           with other settings: norun, nopack, four)
package main

import (
	"bufio"
	"fmt"
	"hash/fnv"
	"math/big"
	"os"
	"runtime/debug"
	"runtime/pprof"
	"strconv"
	"strings"
	"time"
)

const (
	I0 = iota
	I1
	W01
	W10
	BB
	SS
	UU
	GG // on the left stack: a packed sequence of runs (b a^n)^q, n >= 2, that the head only passes through
	HH // the same sequence on the right stack, while the head is left of it
)
const (
	sA = iota
	sB
	sC
	sD
	sE
	sF
)
const TH = 8
const TQ = 4
const PMAX = 60

type Item struct {
	k    uint8
	n, q *big.Int
	g    *Group
}

// Group: runs S_1 .. S_r (left to right).  Passing it leftwards (state D, (10)^3 on the right stack) and rightwards
// (state C) is what the engine's own macros for S and U do run by run; the costs are the sums of theirs.
type Group struct {
	items        []Item
	costL, costR *big.Int
	sig          Hash
	cnt          []*big.Int
}

// Hash: two polynomial hashes (mod 2^64) of the sequence of shape codes; it can be extended by a whole group.
type Hash struct{ h1, h2, p1, p2 uint64 }

const hB1, hB2 = 0x9E3779B97F4A7C15, 0xC2B2AE3D27D4EB4F

func newHash() Hash { return Hash{0, 0, 1, 1} }
func (h *Hash) add(v uint64) {
	v = (v + 0x1234567) * 0xff51afd7ed558ccd
	v ^= v >> 29
	h.h1 = h.h1*hB1 + v
	h.h2 = h.h2*hB2 + (v ^ 0x5555555555555555)
	h.p1 *= hB1
	h.p2 *= hB2
}
func (h *Hash) addHash(g Hash) {
	h.h1 = h.h1*g.p1 + g.h1
	h.h2 = h.h2*g.p2 + g.h2
	h.p1 *= g.p1
	h.p2 *= g.p2
}

func newGroup(items []Item) *Group {
	g := &Group{items: items, costL: new(big.Int), costR: new(big.Int)}
	sb := newHash()
	for _, x := range items {
		if x.k != SS {
			panic("group item")
		}
		n2 := muli(x.n, 2)
		g.costL.Add(g.costL, mul(x.q, addi(n2, 21)))
		g.costR.Add(g.costR, mul(x.q, addi(n2, 5)))
		sigItem(&sb, &g.cnt, x)
	}
	g.sig = sb
	return g
}

var one = big.NewInt(1)
var jumplog = false
var big5 = big.NewInt(5)
var big21 = big.NewInt(21)
var tmpS big.Int
var zero = big.NewInt(0)

func bi(v int64) *big.Int        { return big.NewInt(v) }
func add(a, b *big.Int) *big.Int { return new(big.Int).Add(a, b) }
func sub(a, b *big.Int) *big.Int { return new(big.Int).Sub(a, b) }
func mul(a, b *big.Int) *big.Int { return new(big.Int).Mul(a, b) }
func addi(a *big.Int, v int64) *big.Int {
	return new(big.Int).Add(a, big.NewInt(v))
}
func muli(a *big.Int, v int64) *big.Int {
	return new(big.Int).Mul(a, big.NewInt(v))
}
func cmpi(a *big.Int, v int64) int {
	if a.IsInt64() {
		x := a.Int64()
		if x < v {
			return -1
		} else if x > v {
			return 1
		}
		return 0
	}
	return a.Sign()
}
func eq(a, b *big.Int) bool { return a.Cmp(b) == 0 }

type tr struct {
	w, d, s int
	halt    bool
}

var T [6][2]tr

func parse(m string) {
	for i, g := range strings.Split(m, "_") {
		for r := 0; r < 2; r++ {
			t := g[3*r : 3*r+3]
			if t[0] == '-' {
				T[i][r] = tr{halt: true}
			} else {
				d := -1
				if t[1] == 'R' {
					d = 1
				}
				T[i][r] = tr{w: int(t[0] - '0'), d: d, s: int(t[2] - 'A')}
			}
		}
	}
}

type Sample struct {
	sig   [2]uint64
	sid   int
	cnt   []*big.Int
	steps *big.Int
}
type Pending struct {
	L              []Item
	steps          *big.Int
	hist           []Sample
	nsample, njump int64
	p              int
	J              *big.Int
	d              []*big.Int
	cyc            []int
	i              int
	D1, D2         *big.Int
	start          Sample
}
type Sim struct {
	L, R        []Item
	s           int
	steps       *big.Int
	hist        []Sample
	sigids      map[[2]uint64]int
	njump       int64
	nsample     int64
	nraw        int64
	nbulk       int64
	nroll       int64
	pending     *Pending
	halted      bool
	nojumpUntil int64
	accel, bulk bool
	pack        bool
	nextSid     int
	lowL        int // the least length of L at the end of a step of the current trip
	sigValid    int // the first sigValid tokens of L are those of the last sigCounts
	preHash     []Hash
	preCnt      []int
	lastCnt     []*big.Int
	visits      *big.Int // visits of the right end since the start (not kept through periodic jumps)
	runrule     bool
	lastRun     *runState
	nrun        int64
	four        bool
	npack       int64
	nunpack     int64
}

func NewSim() *Sim {
	return &Sim{s: sA, steps: bi(0), sigids: map[[2]uint64]int{}, nojumpUntil: -1, accel: true, bulk: true, pack: true, runrule: true, visits: bi(0)}
}
func (m *Sim) topL() *Item {
	if len(m.L) == 0 {
		return nil
	}
	return &m.L[len(m.L)-1]
}
func (m *Sim) topR() *Item {
	if len(m.R) == 0 {
		return nil
	}
	return &m.R[len(m.R)-1]
}
func (m *Sim) pushL(x Item) {
	L := m.L
	n := len(L)
	switch x.k {
	case I1:
		if n > 0 && L[n-1].k == I0 {
			m.L = L[:n-1]
			m.pushL(Item{k: W01, n: one})
		} else {
			m.L = append(L, x)
		}
	case I0:
		if n == 0 {
			return
		}
		if n >= 3 && L[n-1].k == I1 && L[n-2].k == W01 && cmpi(L[n-2].n, 1) == 0 && L[n-3].k == I0 {
			m.L = append(L[:n-3], Item{k: BB})
		} else {
			m.L = append(L, x)
		}
	case W01:
		if n > 0 && L[n-1].k == W01 {
			L[n-1] = Item{k: W01, n: add(L[n-1].n, x.n)}
		} else if n > 0 && L[n-1].k == GG && L[n-1].n != nil {
			// a group just passed rightwards: the plain engine has `.. (b a^n)^(q-1) b a^n` there, last block open
			its := L[n-1].g.items
			last := its[len(its)-1]
			m.L = append(L[:n-1], its[:len(its)-1]...)
			if cmpi(last.q, 1) > 0 {
				m.L = append(m.L, Item{k: SS, n: last.n, q: addi(last.q, -1)})
			}
			m.L = append(m.L, Item{k: BB}, Item{k: W01, n: add(last.n, x.n)})
			m.nunpack++
		} else {
			m.L = append(L, x)
		}
	case W10:
		if n > 0 && L[n-1].k == I0 {
			m.L = L[:n-1]
			m.pushL(Item{k: W01, n: x.n})
			m.L = append(m.L, Item{k: I0})
		} else if n == 0 {
			m.L = append(m.L, Item{k: I1})
			if cmpi(x.n, 1) > 0 {
				m.L = append(m.L, Item{k: W01, n: addi(x.n, -1)})
			}
			m.L = append(m.L, Item{k: I0})
		} else if L[n-1].k == W10 {
			L[n-1] = Item{k: W10, n: add(L[n-1].n, x.n)}
		} else {
			m.L = append(L, x)
		}
	default:
		m.L = append(L, x)
	}
}
func (m *Sim) pushR(x Item) {
	R := m.R
	n := len(R)
	switch x.k {
	case I1:
		if n > 0 && R[n-1].k == I0 {
			m.R = R[:n-1]
			m.pushR(Item{k: W10, n: one})
		} else {
			m.R = append(R, x)
		}
	case I0:
		if n > 0 {
			m.R = append(R, x)
		}
	case W10:
		if n > 0 && R[n-1].k == W10 {
			R[n-1] = Item{k: W10, n: add(R[n-1].n, x.n)}
		} else {
			m.R = append(R, x)
		}
	case W01:
		if n > 0 && R[n-1].k == I0 {
			m.R = R[:n-1]
			m.pushR(Item{k: W10, n: x.n})
			m.R = append(m.R, Item{k: I0})
		} else if n == 0 {
			m.R = append(m.R, Item{k: I1})
			if cmpi(x.n, 1) > 0 {
				m.R = append(m.R, Item{k: W10, n: addi(x.n, -1)})
			}
			m.R = append(m.R, Item{k: I0})
		} else if R[n-1].k == W01 {
			R[n-1] = Item{k: W01, n: add(R[n-1].n, x.n)}
		} else {
			m.R = append(R, x)
		}
	default:
		m.R = append(R, x)
	}
}
func (m *Sim) popL() int {
	for {
		n := len(m.L)
		if n == 0 {
			return 0
		}
		x := m.L[n-1]
		m.L = m.L[:n-1]
		switch x.k {
		case I0:
			return 0
		case I1:
			return 1
		case W01, W10:
			if cmpi(x.n, 1) > 0 {
				m.L = append(m.L, Item{k: x.k, n: addi(x.n, -1)})
			}
			if x.k == W01 {
				m.L = append(m.L, Item{k: I0})
				return 1
			}
			m.L = append(m.L, Item{k: I1})
			return 0
		case BB:
			m.L = append(m.L, Item{k: I0}, Item{k: W01, n: one}, Item{k: I1})
			return 0
		case SS:
			if cmpi(x.q, 1) > 0 {
				m.L = append(m.L, Item{k: SS, n: x.n, q: addi(x.q, -1)})
			}
			m.L = append(m.L, Item{k: BB})
			if x.n.Sign() > 0 {
				m.L = append(m.L, Item{k: W01, n: x.n})
			}
			continue
		case GG:
			m.L = append(m.L, x.g.items...)
			m.nunpack++
			continue
		default:
			panic("popL")
		}
	}
}
func (m *Sim) popR() int {
	n := len(m.R)
	if n == 0 {
		return 0
	}
	x := m.R[n-1]
	m.R = m.R[:n-1]
	switch x.k {
	case I0:
		return 0
	case I1:
		return 1
	case W01, W10:
		if cmpi(x.n, 1) > 0 {
			m.R = append(m.R, Item{k: x.k, n: addi(x.n, -1)})
		}
		if x.k == W10 {
			m.R = append(m.R, Item{k: I0})
			return 1
		}
		m.R = append(m.R, Item{k: I1})
		return 0
	case UU:
		if cmpi(x.q, 1) > 0 {
			m.R = append(m.R, Item{k: UU, n: x.n, q: addi(x.q, -1)})
		}
		if x.n.Sign() > 0 {
			m.R = append(m.R, Item{k: W10, n: x.n})
		}
		return 1
	case HH:
		// what the engine leaves on the right stack after passing S_r, .., S_1 leftwards with (10)^3 on top
		its := x.g.items
		for i := len(its) - 1; i >= 0; i-- {
			n2 := addi(its[i].n, 2)
			m.R = append(m.R, Item{k: W10, n: n2}, Item{k: I1})
			if cmpi(its[i].q, 1) > 0 {
				m.R = append(m.R, Item{k: UU, n: n2, q: addi(its[i].q, -1)})
			}
		}
		m.nunpack++
		return m.popR()
	}
	panic("popR")
}

// one (macro) step; returns false on halt
func (m *Sim) step() bool {
	if m.s == sC && len(m.R) > 0 {
		nR := len(m.R)
		top := m.R[nR-1]
		if top.k == W10 {
			m.R = m.R[:nR-1]
			m.pushL(Item{k: W01, n: top.n})
			m.steps.Add(m.steps, tmpS.Lsh(top.n, 1))
			return true
		}
		if top.k == UU && cmpi(top.n, 2) >= 0 {
			m.R = m.R[:nR-1]
			n := addi(top.n, -2)
			q := top.q
			if t := m.topL(); t != nil && t.k == GG {
				g := t.g
				m.L = append(m.L[:len(m.L)-1], g.items...)
				m.nunpack++
			}
			if t := m.topL(); t != nil && t.k == SS && eq(t.n, n) {
				*t = Item{k: SS, n: n, q: add(t.q, q)}
			} else {
				m.L = append(m.L, Item{k: SS, n: n, q: q})
			}
			m.steps.Add(m.steps, mul(q, addi(muli(n, 2), 5)))
			return true
		}
		if top.k == HH {
			g := top.g
			m.R = m.R[:nR-1]
			if t := m.topL(); t != nil && (t.k == GG || (t.k == SS && eq(t.n, g.items[0].n))) {
				// rare: do it run by run, as the U macro would
				if t.k == GG {
					t2 := t.g
					m.L = append(m.L[:len(m.L)-1], t2.items...)
				}
				for _, it := range g.items {
					if t := m.topL(); t != nil && t.k == SS && eq(t.n, it.n) {
						*t = Item{k: SS, n: it.n, q: add(t.q, it.q)}
					} else {
						m.L = append(m.L, it)
					}
				}
				m.nunpack++
			} else {
				m.L = append(m.L, Item{k: GG, g: g, n: one}) // n set: just passed rightwards
			}
			m.steps.Add(m.steps, g.costR)
			return true
		}
		if top.k == I1 && nR >= 2 && m.R[nR-2].k == W10 && cmpi(m.R[nR-2].n, 2) >= 0 {
			k := m.R[nR-2].n
			m.R = m.R[:nR-2]
			m.L = append(m.L, Item{k: BB})
			if cmpi(k, 2) > 0 {
				m.R = append(m.R, Item{k: W10, n: addi(k, -2)})
			}
			m.steps.Add(m.steps, big5)
			return true
		}
	}
	x := m.popR()
	t := T[m.s][x]
	if t.halt {
		m.halted = true
		return false
	}
	m.steps.Add(m.steps, one)
	m.s = t.s
	if t.d == 1 {
		m.pushL(Item{k: uint8(t.w)})
	} else {
		m.pushR(Item{k: uint8(t.w)})
		if t.s == sD {
			for len(m.L) > 0 {
				top := m.L[len(m.L)-1]
				if top.k == I0 || top.k == I1 {
					break
				}
				if top.k == W01 || top.k == W10 {
					if top.k != W01 {
						break
					}
					m.L = m.L[:len(m.L)-1]
					m.pushR(Item{k: W10, n: top.n})
					m.steps.Add(m.steps, tmpS.Lsh(top.n, 1))
				} else if r := m.topR(); r != nil && r.k == W10 {
					k := r.n
					if top.k == BB {
						m.L = m.L[:len(m.L)-1]
						m.R = m.R[:len(m.R)-1]
						if cmpi(k, 1) > 0 {
							m.R = append(m.R, Item{k: W10, n: addi(k, -1)})
						}
						m.R = append(m.R, Item{k: I1}, Item{k: W10, n: bi(3)})
						m.steps.Add(m.steps, big21)
					} else if top.k == SS {
						n, q := top.n, top.q
						m.L = m.L[:len(m.L)-1]
						m.R = m.R[:len(m.R)-1]
						nk := addi(add(n, k), -1)
						if nk.Sign() > 0 {
							m.R = append(m.R, Item{k: W10, n: nk})
						}
						m.R = append(m.R, Item{k: I1})
						if cmpi(q, 1) > 0 {
							m.R = append(m.R, Item{k: UU, n: addi(n, 2), q: addi(q, -1)})
						}
						m.R = append(m.R, Item{k: W10, n: bi(3)})
						m.steps.Add(m.steps, mul(q, addi(muli(n, 2), 21)))
					} else if top.k == GG {
						if cmpi(k, 3) == 0 {
							m.L = m.L[:len(m.L)-1]
							m.R[len(m.R)-1] = Item{k: HH, g: top.g}
							m.R = append(m.R, Item{k: W10, n: bi(3)})
							m.steps.Add(m.steps, top.g.costL)
						} else {
							m.L = append(m.L[:len(m.L)-1], top.g.items...)
							m.nunpack++
						}
					} else {
						break
					}
				} else {
					break
				}
			}
		}
		y := m.popL()
		m.pushR(Item{k: uint8(y)})
	}
	return true
}
func (m *Sim) atEnd() bool {
	if m.s != sB {
		return false
	}
	if len(m.R) == 0 {
		return true
	}
	if len(m.R) <= 2 {
		for _, x := range m.R {
			if x.k != I0 {
				return false
			}
		}
		m.R = m.R[:0]
		return true
	}
	return false
}

// canon(from): the tokens before index `from` are as the last canon left them
func (m *Sim) canon(from int) {
	if from < 0 {
		from = 0
	}
	if from > len(m.L) {
		from = len(m.L)
	}
	if from-1 < m.sigValid {
		m.sigValid = from - 1
		if m.sigValid < 0 {
			m.sigValid = 0
		}
	}
	L := append([]Item(nil), m.L[from:]...)
	out := m.L[:from]
	n := len(L)
	emitS := func(y Item) {
		if len(out) > 0 && out[len(out)-1].k == GG {
			g := out[len(out)-1].g
			if eq(g.items[len(g.items)-1].n, y.n) {
				out = append(out[:len(out)-1], g.items...)
				m.nunpack++
			}
		}
		if len(out) > 0 && out[len(out)-1].k == SS && eq(out[len(out)-1].n, y.n) {
			out[len(out)-1] = Item{k: SS, n: y.n, q: add(out[len(out)-1].q, y.q)}
		} else {
			out = append(out, y)
		}
	}
	for i := 0; i < n; {
		x := L[i]
		if x.k == BB {
			if i+1 < n && L[i+1].k == W01 {
				emitS(Item{k: SS, n: L[i+1].n, q: one})
				i += 2
			} else {
				emitS(Item{k: SS, n: zero, q: one})
				i++
			}
		} else if x.k == SS {
			emitS(x)
			i++
		} else if x.k == GG {
			if len(out) > 0 && (out[len(out)-1].k == GG || (out[len(out)-1].k == SS && eq(out[len(out)-1].n, x.g.items[0].n))) {
				for _, it := range x.g.items {
					emitS(it)
				}
				m.nunpack++
			} else {
				out = append(out, Item{k: GG, g: x.g})
			}
			i++
		} else {
			out = append(out, x)
			i++
		}
	}
	// pack the runs that the head only passes through: those between the first run right of the cursor's block and
	// the end block
	n = len(out)
	if m.pack && n >= 8 && out[n-1].k == I0 && out[n-2].k == SS {
		b := n - 3
		a := b
		loose := 0
		for a >= 0 && (out[a].k == GG || (out[a].k == SS && cmpi(out[a].n, 2) >= 0)) {
			if out[a].k == SS {
				loose++
			}
			a--
		}
		lo := a + 2
		if lo <= b && out[a+1].k == SS {
			loose--
		}
		if loose >= 6 {
			// the costs and the shape code of the new group: those of the old groups plus the new runs
			g := &Group{costL: new(big.Int), costR: new(big.Int), sig: newHash()}
			for i := lo; i <= b; i++ {
				if out[i].k == GG {
					o := out[i].g
					g.items = append(g.items, o.items...)
					g.cnt = append(g.cnt, o.cnt...)
					g.costL.Add(g.costL, o.costL)
					g.costR.Add(g.costR, o.costR)
					g.sig.addHash(o.sig)
				} else {
					x := out[i]
					g.items = append(g.items, x)
					n2 := muli(x.n, 2)
					g.costL.Add(g.costL, mul(x.q, addi(n2, 21)))
					g.costR.Add(g.costR, mul(x.q, addi(n2, 5)))
					sigItem(&g.sig, &g.cnt, x)
				}
			}
			out[lo] = Item{k: GG, g: g}
			out = append(out[:lo+1], out[b+1:]...)
			m.npack++
		}
	}
	m.L = out
}
func itemStr(x Item) string {
	switch x.k {
	case I0:
		return "0"
	case I1:
		return "1"
	case W01, W10:
		c := "a"
		if x.k == W10 {
			c = "A"
		}
		if cmpi(x.n, 1) > 0 {
			return c + "^" + x.n.String()
		}
		return c
	case BB:
		return "b"
	case GG:
		parts := make([]string, len(x.g.items))
		for i, y := range x.g.items {
			parts[i] = itemStr(y)
		}
		return strings.Join(parts, " ")
	case SS:
		inner := "b"
		if cmpi(x.n, 1) > 0 {
			inner = "b a^" + x.n.String()
		} else if cmpi(x.n, 1) == 0 {
			inner = "b a"
		}
		if cmpi(x.q, 1) > 0 {
			return "(" + inner + ")^" + x.q.String()
		}
		return inner
	}
	return "?"
}
func (m *Sim) show() string {
	parts := make([]string, len(m.L))
	for i, x := range m.L {
		parts[i] = itemStr(x)
	}
	return strings.Join(parts, " ")
}

// the shape code of an item: its kind, and its counts when small, their parity when large (>= TH, TQ);
// the large counts are appended to *cntp
func small(n *big.Int, th int64) (uint64, bool) {
	if n.IsInt64() {
		v := n.Int64()
		if v < th {
			return uint64(v), true
		}
	}
	return uint64(n.Bit(0)), false
}
func sigItem(sb *Hash, cntp *[]*big.Int, x Item) {
	switch x.k {
	case I0, I1, BB:
		sb.add(uint64(x.k))
	case W01, W10:
		v, sm := small(x.n, TH)
		if sm {
			sb.add(uint64(x.k) | v<<8)
		} else {
			sb.add(uint64(x.k) | 1<<7 | v<<8)
			*cntp = append(*cntp, x.n)
		}
	case SS:
		v, sm := small(x.n, TH)
		w, sq := small(x.q, TQ)
		code := uint64(x.k) | v<<8
		if !sm {
			code |= 1 << 7
			*cntp = append(*cntp, x.n)
		}
		if sq {
			code |= w << 16
		} else {
			code |= 1 << 6
			*cntp = append(*cntp, x.q)
		}
		sb.add(code)
	default:
		sb.add(99)
	}
}
func (m *Sim) sigCounts() ([2]uint64, []*big.Int) {
	L := m.L
	i0 := m.sigValid
	if i0 > len(L) {
		i0 = len(L)
	}
	if i0 >= len(m.preHash) {
		i0 = len(m.preHash) - 1
	}
	var sb Hash
	var cnt []*big.Int
	if i0 <= 0 {
		i0 = 0
		sb = newHash()
		cnt = make([]*big.Int, 0, 2*len(L)+8)
	} else {
		sb = m.preHash[i0]
		cnt = make([]*big.Int, m.preCnt[i0], 2*len(L)+8)
		copy(cnt, m.lastCnt[:m.preCnt[i0]])
	}
	if cap(m.preHash) < len(L)+1 {
		nh := make([]Hash, len(L)+1, 2*len(L)+16)
		copy(nh, m.preHash)
		m.preHash = nh
		nc := make([]int, len(L)+1, 2*len(L)+16)
		copy(nc, m.preCnt)
		m.preCnt = nc
	} else {
		m.preHash = m.preHash[:len(L)+1]
		m.preCnt = m.preCnt[:len(L)+1]
	}
	for i := i0; i < len(L); i++ {
		m.preHash[i] = sb
		m.preCnt[i] = len(cnt)
		x := L[i]
		if x.k == GG {
			sb.addHash(x.g.sig)
			cnt = append(cnt, x.g.cnt...)
		} else {
			sigItem(&sb, &cnt, x)
		}
	}
	m.preHash[len(L)] = sb
	m.preCnt[len(L)] = len(cnt)
	m.sigValid = len(L)
	m.lastCnt = cnt
	return [2]uint64{sb.h1, sb.h2}, cnt
}
func (m *Sim) setCounts(cnt []*big.Int) {
	m.sigValid = 0
	// groups: unchanged counts stay packed; otherwise unpack first
	i := 0
	changed := false
	for _, x := range m.L {
		switch x.k {
		case W01, W10:
			if cmpi(x.n, TH) >= 0 {
				i++
			}
		case SS:
			if cmpi(x.n, TH) >= 0 {
				i++
			}
			if cmpi(x.q, TQ) >= 0 {
				i++
			}
		case GG:
			for _, c := range x.g.cnt {
				if c != cnt[i] && c.Cmp(cnt[i]) != 0 {
					changed = true
				}
				i++
			}
		}
	}
	if changed {
		nl := make([]Item, 0, len(m.L)+16)
		for _, x := range m.L {
			if x.k == GG {
				nl = append(nl, x.g.items...)
			} else {
				nl = append(nl, x)
			}
		}
		m.L = nl
		m.nunpack++
	}
	i = 0
	L := m.L
	for j, x := range L {
		switch x.k {
		case W01, W10:
			if cmpi(x.n, TH) >= 0 {
				L[j] = Item{k: x.k, n: cnt[i]}
				i++
			}
		case SS:
			n, q := x.n, x.q
			if cmpi(n, TH) >= 0 {
				n = cnt[i]
				i++
			}
			if cmpi(q, TQ) >= 0 {
				q = cnt[i]
				i++
			}
			L[j] = Item{k: SS, n: n, q: q}
		case GG:
			i += len(x.g.cnt)
		}
	}
}

// run to the next visit of the right end; false on halt
func (m *Sim) trip() bool {
	m.lowL = len(m.L)
	for {
		if !m.step() {
			return false
		}
		if len(m.L) < m.lowL {
			m.lowL = len(m.L)
		}
		if m.atEnd() {
			break
		}
	}
	m.nraw++
	m.canon(m.lowL - 3)
	return true
}

type feedShape struct {
	ok      bool
	i       int
	sep     bool
	k, m, M *big.Int
	c       int
}

func (m *Sim) feedshape() feedShape {
	L := m.L
	n := len(L)
	if n < 5 || L[n-1].k != I0 {
		return feedShape{}
	}
	e := L[n-2]
	var i int
	var sep bool
	var M *big.Int
	if e.k == W01 {
		i = n - 2
	} else if e.k == SS && cmpi(e.q, 1) == 0 {
		i = n - 3
		for i >= 0 && (L[i].k == GG || (L[i].k == SS && cmpi(L[i].n, 2) >= 0)) {
			i--
		}
		if i < 2 || L[i].k != W01 {
			return feedShape{}
		}
		sep = true
		M = e.n
	} else {
		return feedShape{}
	}
	c := L[i-1]
	if c.k != I0 && c.k != I1 {
		return feedShape{}
	}
	lb := L[i-2]
	if lb.k != W01 && lb.k != SS {
		return feedShape{}
	}
	return feedShape{ok: true, i: i, sep: sep, k: lb.n, c: int(c.k), m: L[i].n, M: M}
}
func (m *Sim) event() bool {
	var f0 feedShape
	if m.bulk {
		f0 = m.feedshape()
	}
	s0 := new(big.Int).Set(m.steps)
	if !m.trip() {
		return false
	}
	m.visits = addi(m.visits, 1)
	if !f0.ok {
		return true
	}
	f1 := m.feedshape()
	if !f1.ok {
		return true
	}
	g := int64(2)
	if f1.sep {
		g = 4
	}
	if f1.sep != f0.sep || !eq(f1.k, addi(f0.k, -1)) || f1.c != 1-f0.c || !eq(f1.m, addi(f0.m, g)) {
		return true
	}
	j := f1.k // the feed rule needs one copy left of the cursor per visit: k visits (k-1 if the block would vanish)
	if m.L[f1.i-2].k == W01 {
		j = addi(f1.k, -1)
	}
	if f1.sep {
		if !eq(f1.M, addi(f0.M, -2)) {
			return true
		}
		j2 := new(big.Int).Rsh(f1.M, 1) // and 2 copies of the end block per visit
		if j2.Cmp(j) < 0 {
			j = j2
		}
	}
	if j.Sign() < 1 {
		return true
	}
	L := m.L
	i := f1.i
	lb := L[i-2]
	if lb.k == W01 {
		L[i-2] = Item{k: W01, n: sub(f1.k, j)}
	} else if cmpi(lb.q, 1) > 0 {
		nl := make([]Item, 0, len(L)+1)
		nl = append(nl, L[:i-2]...)
		nl = append(nl, Item{k: SS, n: f1.k, q: addi(lb.q, -1)}, Item{k: SS, n: sub(f1.k, j), q: one})
		nl = append(nl, L[i-1:]...)
		L = nl
		m.L = L
		i++
	} else {
		L[i-2] = Item{k: SS, n: sub(f1.k, j), q: one}
	}
	c := f1.c
	if j.Bit(0) == 1 {
		c ^= 1
	}
	L[i-1] = Item{k: uint8(c)}
	L[i] = Item{k: W01, n: add(f1.m, muli(j, g))}
	if f1.sep {
		L[len(L)-2] = Item{k: SS, n: sub(f1.M, muli(j, 2)), q: one}
	}
	jj := j
	if f1.c != 1 {
		jj = addi(j, 1)
	}
	h1 := new(big.Int).Rsh(jj, 1)
	h2 := new(big.Int).Rsh(addi(jj, 1), 1)
	ds := sub(m.steps, s0)
	m.steps.Add(m.steps, add(mul(j, ds), muli(mul(h1, h2), 16)))
	m.nbulk++
	m.visits = add(m.visits, j)
	m.canon(f1.i - 4)
	return true
}

// runState: the cursor stands directly after a separator, with a run (b a^n)^q (n even, >= 8) left of that separator:
//
//	.. (b a^n)^q b c a^m Y a^M 0 B>        Y: separators and blocks only, at least one separator
type runState struct {
	i            int // index of the cursor in L
	n, q, m, M   *big.Int
	c            int
	steps, visit *big.Int
}

func (m *Sim) runShape() *runState {
	L := m.L
	n := len(L)
	if n < 6 || L[n-1].k != I0 || L[n-2].k != SS || cmpi(L[n-2].q, 1) != 0 {
		return nil
	}
	i := n - 3
	for i >= 0 && (L[i].k == GG || (L[i].k == SS && cmpi(L[i].n, 2) >= 0)) {
		i--
	}
	if i < 4 || L[i].k != W01 || cmpi(L[i].n, 2) < 0 || i == n-3+1 {
		return nil
	}
	i-- // the cursor
	if !isInt(L[i]) {
		return nil
	}
	b, r := L[i-1], L[i-2]
	if b.k != SS || b.n.Sign() != 0 || cmpi(b.q, 1) != 0 {
		return nil
	}
	if r.k != SS || cmpi(r.n, 8) < 0 || r.n.Bit(0) != 0 {
		return nil
	}
	return &runState{i: i, n: r.n, q: r.q, m: L[i+1].n, M: L[n-2].n, c: int(L[i].k), steps: new(big.Int).Set(m.steps), visit: m.visits}
}

// The run rule.  One period takes the cursor across one block of the run, in n+2 visits (two for the separator, n
// feedings); it costs the end block 2(n+2) copies and leaves a block of 4n+6 behind:
//
//	(b a^n)^q b 0 a^m Y a^M      ->  (b a^n)^(q-1) b 0 a^(4n+6) b a^m     Y a^(M-2n-4)
//	(b a^n)^q b 1 a^m Y a^M      ->  (b a^n)^(q-1) b 1 a^(4n+1) b a^(m+5) Y a^(M-2n-4)
//
// (the rules hop0a, hop0b, hop1a, hop1b and feedb of lean/Rules.lean, with any Y).  When the last period simulated
// visit by visit did exactly this, J more periods are applied at once, J <= q and J <= M / (2n+4).  Every visit of
// a period finds 2n+2 more copies of `a` and one more separator between the cursor and the right end than the same
// visit of the period before, which costs 4 steps per copy and 26 per separator: the periods' step counts grow by
// (n+2)(8n+34) each.
func (m *Sim) tryRun() bool {
	cur := m.runShape()
	if cur == nil {
		return false // between two such moments (the visits of one period) lastRun is kept
	}
	prev := m.lastRun
	m.lastRun = cur
	if prev == nil || !m.runrule {
		return false
	}
	n := cur.n
	delta := addi(muli(n, 2), 4)
	if cur.i != prev.i || !eq(n, prev.n) || cur.c != prev.c || !eq(cur.q, addi(prev.q, -1)) ||
		!eq(cur.M, sub(prev.M, delta)) || !eq(sub(cur.visit, prev.visit), addi(n, 2)) {
		return false
	}
	B := addi(muli(n, 4), 6)
	mm, mold := B, prev.m
	if cur.c == 1 {
		mm, mold = addi(muli(n, 4), 1), addi(prev.m, 5)
	}
	L := m.L
	i := cur.i
	nx := L[i+2]
	if !eq(cur.m, mm) || nx.k != SS || !eq(nx.n, mold) {
		return false
	}
	J := new(big.Int).Div(cur.M, delta)
	if cur.q.Cmp(J) < 0 {
		J = cur.q
	}
	if J.Sign() < 1 {
		return false
	}
	s1 := sub(cur.steps, prev.steps)
	D2 := mul(addi(n, 2), addi(muli(n, 8), 34))
	tri := new(big.Int).Rsh(mul(J, addi(J, 1)), 1)
	m.steps.Add(m.steps, add(mul(J, s1), mul(tri, D2)))
	m.visits = add(m.visits, mul(J, addi(n, 2)))
	nl := make([]Item, 0, len(L)+1)
	nl = append(nl, L[:i-2]...)
	if q2 := sub(cur.q, J); q2.Sign() > 0 {
		nl = append(nl, Item{k: SS, n: n, q: q2})
	}
	nl = append(nl, L[i-1], L[i], L[i+1])
	if eq(nx.n, B) {
		nl = append(nl, Item{k: SS, n: B, q: add(nx.q, J)})
	} else {
		nl = append(nl, Item{k: SS, n: B, q: J}, nx)
	}
	nl = append(nl, L[i+3:]...)
	nl[len(nl)-2] = Item{k: SS, n: sub(cur.M, mul(J, delta)), q: one}
	m.L = nl
	m.canon(i - 4)
	m.lastRun = nil
	m.nrun++
	return true
}
func (m *Sim) sample() {
	sig, cnt := m.sigCounts()
	sid, ok := m.sigids[sig]
	if !ok {
		if len(m.sigids) >= 1<<20 { // ids are only compared within the last samples: forget the old shapes
			m.sigids = map[[2]uint64]int{}
			for _, hs := range m.hist {
				m.sigids[hs.sig] = hs.sid
			}
		}
		m.nextSid++
		sid = m.nextSid
		m.sigids[sig] = sid
	}
	if len(m.hist) >= 1024 { // only the last 3*PMAX+1 samples are ever read
		m.hist = append([]Sample(nil), m.hist[len(m.hist)-512:]...)
	}
	m.hist = append(m.hist, Sample{sig, sid, cnt, new(big.Int).Set(m.steps)})
	m.nsample++
}
func diffs(a, b []*big.Int) []*big.Int {
	if len(a) != len(b) {
		return nil
	}
	d := make([]*big.Int, len(a))
	for i := range a {
		d[i] = sub(a[i], b[i])
	}
	return d
}
func sameVec(a, b []*big.Int) bool {
	if a == nil || b == nil || len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i].Cmp(b[i]) != 0 {
			return false
		}
	}
	return true
}

var tmpA, tmpB big.Int

// a - b == b - c, entry by entry, without allocating
func sameDiff(a, b, c []*big.Int) bool {
	if len(a) != len(b) || len(b) != len(c) {
		return false
	}
	for i := range a {
		if a[i] == b[i] && b[i] == c[i] {
			continue
		}
		tmpA.Sub(a[i], b[i])
		tmpB.Sub(b[i], c[i])
		if tmpA.Cmp(&tmpB) != 0 {
			return false
		}
	}
	return true
}
func (m *Sim) tryJump() bool {
	h := m.hist
	t := len(h) - 1
	if m.pending != nil || m.nsample <= m.nojumpUntil {
		return false
	}
	sid := h[t].sid
	if m.four {
		return m.tryJump4()
	}
	// a period p seen twice: samples t-2p, t-p, t with the same shapes in between and the same change of the counts.
	// The step counts of the periods are extrapolated linearly (first difference D1, second difference D2).  Nothing
	// here is trusted: the period after the jump must reproduce shapes, changes and step count (checkPending).
	pm := t / 2
	if pm > PMAX {
		pm = PMAX
	}
	for p := 1; p <= pm; p++ {
		if h[t-p].sid != sid || h[t-2*p].sid != sid {
			continue
		}
		ok := true
		for i := 1; i < p; i++ {
			if h[t-i-p].sid != h[t-i].sid {
				ok = false
				break
			}
		}
		if !ok {
			continue
		}
		c0, c1, c2 := h[t].cnt, h[t-p].cnt, h[t-2*p].cnt
		if !sameDiff(c0, c1, c2) {
			continue
		}
		s0, s1, s2 := h[t].steps, h[t-p].steps, h[t-2*p].steps
		D1 := sub(s0, s1)
		D2 := sub(D1, sub(s1, s2))
		any := false
		var J *big.Int
		var thr []int64
		for i := range c0 {
			if c0[i] == c1[i] {
				continue
			}
			dd := tmpA.Sub(c0[i], c1[i])
			if dd.Sign() != 0 {
				any = true
			}
			if dd.Sign() < 0 {
				// the count must stay large (same shape) during the J periods and the period that validates them
				if thr == nil {
					thr = m.thresholds()
				}
				nd := new(big.Int).Neg(dd)
				j := new(big.Int).Div(addi(c0[i], -thr[i]), nd) // floor
				if J == nil || j.Cmp(J) < 0 {
					J = j
				}
			}
		}
		if !any || J == nil {
			continue
		}
		J = addi(J, -1)
		if cmpi(J, 2) < 0 {
			continue
		}
		m.doJump(p, J, diffs(c0, c1), D1, D2)
		return true
	}
	return false
}

// the smallest values the large counts may take without changing the shape, in the order of sigCounts
func (m *Sim) thresholds() []int64 {
	out := make([]int64, 0, 2*len(m.L))
	one := func(x Item) {
		switch x.k {
		case W01, W10:
			if cmpi(x.n, TH) >= 0 {
				out = append(out, TH)
			}
		case SS:
			if cmpi(x.n, TH) >= 0 {
				out = append(out, TH)
			}
			if cmpi(x.q, TQ) >= 0 {
				out = append(out, TQ)
			}
		}
	}
	for _, x := range m.L {
		if x.k == GG {
			for _, y := range x.g.items {
				one(y)
			}
		} else {
			one(x)
		}
	}
	return out
}

// the detection of py/fsim.py: a period seen three times
func (m *Sim) tryJump4() bool {
	h := m.hist
	t := len(h) - 1
	if m.pending != nil || m.nsample <= m.nojumpUntil {
		return false
	}
	sid := h[t].sid
	pm := t / 3
	if pm > PMAX {
		pm = PMAX
	}
	for p := 1; p <= pm; p++ {
		if h[t-p].sid != sid || h[t-2*p].sid != sid || h[t-3*p].sid != sid {
			continue
		}
		ok := true
		for i := 1; i < p; i++ {
			a := h[t-i].sid
			if h[t-i-p].sid != a || h[t-i-2*p].sid != a {
				ok = false
				break
			}
		}
		if !ok {
			continue
		}
		c0, c1, c2, c3 := h[t].cnt, h[t-p].cnt, h[t-2*p].cnt, h[t-3*p].cnt
		if !sameDiff(c0, c1, c2) || !sameDiff(c1, c2, c3) {
			continue
		}
		for i := 1; i < p; i++ {
			if !sameDiff(h[t-i].cnt, h[t-i-p].cnt, h[t-i-2*p].cnt) {
				ok = false
				break
			}
		}
		if !ok {
			continue
		}
		s0, s1, s2, s3 := h[t].steps, h[t-p].steps, h[t-2*p].steps, h[t-3*p].steps
		D1 := sub(s0, s1)
		D2 := sub(D1, sub(s1, s2))
		if D2.Cmp(sub(sub(s1, s2), sub(s2, s3))) != 0 {
			continue
		}
		any := false
		var J *big.Int
		for i := range c0 {
			if c0[i] == c1[i] {
				continue
			}
			dd := tmpA.Sub(c0[i], c1[i])
			if dd.Sign() != 0 {
				any = true
			}
			if dd.Sign() < 0 {
				nd := new(big.Int).Neg(dd)
				num := sub(addi(c0[i], -TH-2), muli(nd, 2))
				j := new(big.Int).Div(num, nd) // Euclidean = floor for nd > 0
				if J == nil || j.Cmp(J) < 0 {
					J = j
				}
			}
		}
		if !any || J == nil {
			continue
		}
		J = addi(J, -1)
		if cmpi(J, 2) < 0 {
			continue
		}
		m.doJump(p, J, diffs(c0, c1), D1, D2)
		return true
	}
	return false
}
func (m *Sim) doJump(p int, J *big.Int, d []*big.Int, D1, D2 *big.Int) {
	m.lastRun = nil
	h := m.hist
	t := len(h) - 1
	pd := &Pending{L: append([]Item(nil), m.L...), steps: new(big.Int).Set(m.steps), hist: append([]Sample(nil), h...), nsample: m.nsample,
		njump: m.njump, p: p, J: J, d: d, D2: D2}
	c0 := h[t].cnt
	nc := make([]*big.Int, len(c0))
	for i := range c0 {
		nc[i] = add(c0[i], mul(J, d[i]))
	}
	m.setCounts(nc)
	tri := new(big.Int).Rsh(mul(J, addi(J, 1)), 1)
	m.steps.Add(m.steps, add(mul(J, D1), mul(tri, D2)))
	m.njump++
	pd.cyc = make([]int, p)
	for i := 1; i <= p; i++ {
		pd.cyc[i-1] = h[t-p+i].sid
	}
	pd.D1 = add(D1, mul(J, D2))
	m.pending = pd
	m.hist = nil
	m.sample()
	pd.start = m.hist[len(m.hist)-1]
}
func (m *Sim) checkPending() {
	pd := m.pending
	if pd == nil {
		return
	}
	cur := m.hist[len(m.hist)-1]
	if cur.sid != pd.cyc[pd.i] {
		m.rollback()
		return
	}
	pd.i++
	if pd.i == pd.p {
		if !sameVec(diffs(cur.cnt, pd.start.cnt), pd.d) || sub(cur.steps, pd.start.steps).Cmp(add(pd.D1, pd.D2)) != 0 {
			m.rollback()
			return
		}
		m.pending = nil
	}
}
func (m *Sim) rollback() {
	pd := m.pending
	m.L = append([]Item(nil), pd.L...)
	m.steps = new(big.Int).Set(pd.steps)
	m.sigValid = 0
	m.hist = append([]Sample(nil), pd.hist...)
	m.nsample = pd.nsample
	m.njump = pd.njump
	m.R = m.R[:0]
	m.s = sB
	m.pending = nil
	m.lastRun = nil
	m.nroll++
	m.halted = false
	J := new(big.Int).Rsh(pd.J, 1)
	if cmpi(J, 2) >= 0 {
		m.doJump(pd.p, J, pd.d, sub(pd.D1, mul(pd.J, pd.D2)), pd.D2)
	} else {
		m.nojumpUntil = m.nsample + int64(3*pd.p) + 2
	}
}

func isInt(x Item) bool { return x.k == I0 || x.k == I1 }

func tail(m *Sim, w int) string {
	L := m.L
	a := len(L) - w
	if a < 0 {
		a = 0
	}
	parts := []string{}
	for _, x := range L[a:] {
		s := itemStr(x)
		parts = append(parts, s)
	}
	return abbreviate(strings.Join(parts, " "))
}
func abbreviate(s string) string {
	var sb strings.Builder
	i := 0
	for i < len(s) {
		j := i
		for j < len(s) && s[j] >= '0' && s[j] <= '9' {
			j++
		}
		if j-i > 12 {
			sb.WriteString(fmt.Sprintf("%s..(%dd)", s[i:i+4], j-i))
		} else if j > i {
			sb.WriteString(s[i:j])
		}
		if j < len(s) {
			sb.WriteByte(s[j])
		}
		i = j + 1
	}
	return sb.String()
}
func ctx(L []Item, i, w int) string {
	a, b := i-w, i+w+1
	if a < 0 {
		a = 0
	}
	if b > len(L) {
		b = len(L)
	}
	parts := []string{}
	for _, x := range L[a:b] {
		parts = append(parts, itemStr(x))
	}
	return abbreviate(strings.Join(parts, " "))
}

// expand: the cells of an item of the left stack, left to right
func expand(x Item) string {
	switch x.k {
	case I0:
		return "0"
	case I1:
		return "1"
	case W01:
		return strings.Repeat("01", int(x.n.Int64()))
	case W10:
		return strings.Repeat("10", int(x.n.Int64()))
	case BB:
		return "00110"
	case SS:
		return strings.Repeat("00110"+strings.Repeat("01", int(x.n.Int64())), int(x.q.Int64()))
	case GG:
		var sb strings.Builder
		for _, y := range x.g.items {
			sb.WriteString(expand(y))
		}
		return sb.String()
	}
	panic("expand")
}
func digits(x *big.Int) int { return len(x.String()) }

func main() {
	parse("1RB1RF_1RC0RE_1LD0RB_1RE0LC_1RA0LE_0RC---")
	// usage: fsim DIGITS [raw|nobulk|quiet|full]...   run until the step count has more than DIGITS digits
	nd, _ := strconv.Atoi(os.Args[1])
	if pf := os.Getenv("FSIM_PROF"); pf != "" {
		f, _ := os.Create(pf)
		pprof.StartCPUProfile(f)
		defer pprof.StopCPUProfile()
	}
	m := NewSim()
	quiet, full, births, heads := false, false, false, false
	cf := false
	lastHead := ""
	trace, ntrace := 0, 0
	pairlog := false
	var arrW *bufio.Writer
	prevCi := -1
	leftlog := false
	var ring []string
	nstuck := 0
	var traceB int64
	ntraceMax := 3000
	for _, a := range os.Args[2:] {
		switch a {
		case "raw":
			m.accel = false
		case "nobulk":
			m.bulk = false
		case "nopack":
			m.pack = false
		case "four":
			m.four = true
		case "norun":
			m.runrule = false
		case "quiet":
			quiet = true
		case "cf":
			cf = true
		case "full":
			full = true
		case "births":
			births = true
		case "heads":
			heads = true
		case "pairlog":
			pairlog = true
		case "jumplog":
			jumplog = true
		case "leftlog":
			leftlog = true
		default:
			if strings.HasPrefix(a, "arr=") {
				fh, err := os.Create(a[4:])
				if err != nil {
					panic(err)
				}
				defer fh.Close()
				arrW = bufio.NewWriter(fh)
				defer arrW.Flush()
			}
			if strings.HasPrefix(a, "trace=") {
				trace, _ = strconv.Atoi(a[6:])
			}
			if strings.HasPrefix(a, "traceb=") {
				f := strings.Split(a[7:], ",")
				tb, _ := strconv.Atoi(f[0])
				traceB = int64(tb)
				ntraceMax, _ = strconv.Atoi(f[1])
			}
		}
	}
	limit := new(big.Int).Exp(bi(10), bi(int64(nd)), nil)
	t0 := time.Now()
	debug.SetGCPercent(800)
	// dump=FILE,LO,HI: write "steps hash-of-tape" for every visit stopped at with 10^LO <= steps < 10^HI (no jump
	// waiting for validation), to compare runs made with different settings
	var dumpW *bufio.Writer
	var dumpLo, dumpHi *big.Int
	for _, a := range os.Args[2:] {
		if strings.HasPrefix(a, "dump=") {
			f := strings.Split(a[5:], ",")
			fh, err := os.Create(f[0])
			if err != nil {
				panic(err)
			}
			defer fh.Close()
			dumpW = bufio.NewWriter(fh)
			defer dumpW.Flush()
			lo, _ := strconv.Atoi(f[1])
			hi, _ := strconv.Atoi(f[2])
			dumpLo = new(big.Int).Exp(bi(10), bi(int64(lo)), nil)
			dumpHi = new(big.Int).Exp(bi(10), bi(int64(hi)), nil)
		}
	}
	if len(os.Args) > 2 && os.Args[2] == "check0" {
		// check0: the plain rope engine (no bulk feeding, no packing, no jumps) against a cell-by-cell simulator of
		// the machine table, comparing the whole tape and the state at every visit of the right end
		a := NewSim()
		a.accel, a.bulk, a.pack, a.runrule = false, false, false, false
		tape := make([]byte, 1<<16)
		off := 1 << 15
		pos, st := off, sA
		var ns int64
		var ncmp int64
		for a.steps.Cmp(limit) < 0 {
			if !a.event() {
				panic("halt")
			}
			target := a.steps.Int64()
			for ns < target {
				t := T[st][tape[pos]]
				if t.halt {
					panic("cell sim halt")
				}
				tape[pos] = byte(t.w)
				pos += t.d
				st = t.s
				ns++
				if pos <= 0 || pos >= len(tape)-1 {
					nt := make([]byte, 2*len(tape))
					copy(nt[len(tape)/2:], tape)
					pos += len(tape) / 2
					off += len(tape) / 2
					tape = nt
				}
			}
			var sb strings.Builder
			for _, x := range a.L {
				sb.WriteString(expand(x))
			}
			want := strings.TrimLeft(sb.String(), "0")
			var gb strings.Builder
			for i := 0; i < pos; i++ {
				gb.WriteByte('0' + tape[i])
			}
			got := strings.TrimLeft(gb.String(), "0")
			for i := pos; i < len(tape); i++ {
				if tape[i] != 0 {
					fmt.Printf("MISMATCH: cells right of the head at step %d\n", ns)
					os.Exit(1)
				}
			}
			if st != a.s || st != sB || got != want {
				fmt.Printf("MISMATCH at step %d (visit %d)\n", ns, ncmp)
				os.Exit(1)
			}
			ncmp++
		}
		fmt.Printf("ok: %d visits compared cell by cell (tape and state) up to step %s\n", ncmp, a.steps)
		return
	}
	if len(os.Args) > 2 && (os.Args[2] == "check1" || os.Args[2] == "check2") {
		// check1: bulk feeding against the plain engine; check2: jumps against bulk feeding only.  Compared at every
		// event of the faster one (for check2: when no jump is waiting for its validation).
		a, b := NewSim(), NewSim()
		a.accel = os.Args[2] == "check2"
		b.accel = false
		b.pack = false
		b.bulk = os.Args[2] == "check2"
		var ncmp, nskip int64
		for a.steps.Cmp(limit) < 0 {
			if !a.event() {
				panic("halt")
			}
			a.sample()
			a.checkPending()
			if a.pending == nil {
				for b.steps.Cmp(a.steps) < 0 {
					if !b.event() {
						panic("halt")
					}
				}
				if b.steps.Cmp(a.steps) > 0 {
					nskip++ // the slow one fed in bulk past this step
				} else if a.show() != b.show() {
					fmt.Printf("MISMATCH at steps %s / %s\n%s\n%s\n", a.steps, b.steps, a.show(), b.show())
					os.Exit(1)
				}
				if b.steps.Cmp(a.steps) == 0 {
					ncmp++
				}
			}
			if a.accel {
				if a.pending == nil && a.tryRun() {
					a.hist = nil
					a.sample()
				} else {
					a.tryJump()
				}
			}
		}
		fmt.Printf("ok: %d comparisons (%d steps not comparable) up to step %s; fast: %d visits, %d bulk, %d jumps, %d rollbacks; slow: %d visits, %d bulk\n",
			ncmp, nskip, a.steps, a.nraw, a.nbulk, a.njump, a.nroll, b.nraw, b.nbulk)
		return
	}
	var nbirth, nmidhop, npair, ntriple, nother int64
	pairPrev := false
	lastReport := 0
	for {
		if !m.event() {
			if m.pending != nil {
				// a halt inside the period that validates a jump: the jump is not validated; redo without it
				m.rollback()
				continue
			}
			fmt.Printf("HALT at step %s (the halting transition is not counted; steps done: this minus 1)\n", addi(m.steps, 1).String())
			fmt.Printf("tape left of the head at the last visit form: %s\n", abbreviate(m.show()))
			break
		}
		m.sample()
		m.checkPending()
		L := m.L
		n := len(L)
		// statistics (on the visits simulated one by one)
		pair := false
		for i := 2; i+1 < n; i++ {
			if L[i].k == I1 && L[i+1].k == I1 {
				pair = true
				if i+2 < n && L[i+2].k == I1 {

					ntriple++
					fmt.Printf("TRIPLE steps~1e%d pending=%v | %s | end: %s\n", digits(m.steps)-1, m.pending != nil, ctx(L, i, 4), tail(m, 3))
					act := true
					for j := i + 3; j < n-1; j++ {
						if isInt(L[j]) {
							act = false
						}
					}
					if L[n-1].k == I0 && L[n-2].k == SS && cmpi(L[n-2].q, 1) == 0 {
						M := L[n-2].n
						fmt.Printf("MARGIN triple=%d steps~1e%d active=%v endblock M has %d digits, M mod 8 = %d, visits to the next birth >= M/2 = %s\n", ntriple, digits(m.steps)-1, act, digits(M), new(big.Int).Mod(M, bi(8)).Int64(), abbreviate(new(big.Int).Rsh(M, 1).String()))
						if cf && act && m.pending == nil {
							reportCF(ntriple, L, m.steps)
						}
					} else {
						fmt.Printf("MARGIN triple=%d end not of the form b a^M 0: %s\n", ntriple, tail(m, 3))
					}
				}
				break
			}
		}
		if pair && !pairPrev {
			npair++
		}
		pairPrev = pair
		if n >= 3 && L[n-1].k == I1 && L[n-2].k == W01 && cmpi(L[n-2].n, 1) == 0 && L[n-3].k == I0 {
			nbirth++
			// nearest single cell left of the new cursor
			i := n - 4
			for i >= 0 && !isInt(L[i]) {
				i--
			}
			if heads {
				b := 7
				if b > n {
					b = n
				}
				parts := []string{}
				for _, x := range L[:b] {
					parts = append(parts, itemStr(x))
				}
				hd := abbreviate(strings.Join(parts, " "))
				if hd != lastHead {
					fmt.Printf("HEAD #%d 1e%d | %s\n", nbirth, digits(m.steps)-1, hd)
					lastHead = hd
				}
			}
			if births {
				fmt.Printf("B #%d 1e%d pend=%v len=%d | %s\n", nbirth, digits(m.steps)-1, m.pending != nil, n, ctx(L, i, 3))
			}
			if i > 0 && (isInt(L[i-1]) || (i+1 < n && isInt(L[i+1]))) {
				c := ctx(L, i, 4)
				if strings.Contains(c, "0 a 1 1 a") {
					nmidhop++
					fmt.Printf("BIRTH mid-hop #%d steps~1e%d pending=%v | %s\n", nbirth, digits(m.steps)-1, m.pending != nil, c)
				} else {
					nother++
					if !quiet {
						fmt.Printf("BIRTH other #%d steps~1e%d pending=%v | %s\n", nbirth, digits(m.steps)-1, m.pending != nil, c)
					}
				}
			}
		}
		if arrW != nil {
			ci := -1
			for j := n - 2; j >= 2; j-- {
				if isInt(L[j]) {
					ci = j
					break
				}
			}
			if ci >= 0 && ci <= 14 && (prevCi > 14 || prevCi < 0) && n > 30 {
				e := "?"
				if L[n-1].k == I0 && L[n-2].k == SS {
					e = L[n-2].n.String()
				}
				parts := []string{}
				for _, x := range L[:ci+3] {
					parts = append(parts, itemStr(x))
				}
				fmt.Fprintf(arrW, "ARR %d %d %d %s | %s\n", digits(m.steps)-1, nbirth, ci, e, strings.Join(parts, " "))
			}
			prevCi = ci
		}
		if leftlog {
			// the active cursor has just made the first visit of a crossing (`0 a 1 1 a` or `0 0`) near the left end
			ci := -1
			for j := n - 2; j >= 2; j-- {
				if isInt(L[j]) {
					ci = j
					break
				}
			}
			if ci >= 2 && ci <= 14 && isInt(L[ci-1]) && ((L[ci].k == I1 && L[ci-1].k == I1) || (L[ci].k == I0 && L[ci-1].k == I0)) {
				e := "?"
				if L[n-1].k == I0 && L[n-2].k == SS {
					e = L[n-2].n.String()
					if len(e) > 8 {
						e = fmt.Sprintf("%dd", len(e))
					}
				} else {
					e = "END:" + tail(m, 3)
					if len(e) > 60 {
						e = e[:60]
					}
				}
				fmt.Printf("LEFT 1e%d cur@%d births %d end=%s | %s\n", digits(m.steps)-1, ci, nbirth, e, ctx(L, ci, 4)[:min(150, len(ctx(L, ci, 4)))])
			}
		}
		if pairlog {
			// a pair `1 1` with a cursor somewhere right of it
			pi := -1
			for i := 2; i+1 < n; i++ {
				if L[i].k == I1 && L[i+1].k == I1 {
					pi = i
					break
				}
			}
			stuck := false
			ci := -1
			if pi >= 0 {
				for j := n - 2; j > pi+1; j-- {
					if isInt(L[j]) {
						stuck = true
						ci = j
						break
					}
				}
			}
			if stuck {
				isb := n >= 3 && L[n-1].k == I1 && L[n-2].k == W01
				line := fmt.Sprintf("  ev %d births %d cur@%d/%d pair@%d birth=%v | %s | end %s", m.nsample, nbirth, ci, n, pi, isb, ctx(L, ci, 3), tail(m, 3))
				ring = append(ring, line)
				if len(ring) > 60 {
					ring = ring[1:]
				}
				nstuck++
			} else if len(ring) > 0 {
				fmt.Printf("PAIRLOG: stuck for %d events, the last ones:\n%s\n  then: %s\n", nstuck, strings.Join(ring, "\n"), abbreviate(m.show()[:min(len(m.show()), 400)]))
				ring = nil
				nstuck = 0
			}
		}
		if (trace > 0 && digits(m.steps) > trace) || (traceB > 0 && nbirth >= traceB) {
			i := n - 1
			for i > 0 && !isInt(L[i-1]) {
				i--
			}
			fmt.Printf("EV %d bulk=%d jumps=%d births=%d curpos=%d/%d | %s\n", m.nsample, m.nbulk, m.njump, nbirth, n-i, n, ctx(L, i-1, 3))
			ntrace++
			if ntrace > ntraceMax {
				return
			}
		}
		if dumpW != nil && m.pending == nil && m.steps.Cmp(dumpLo) >= 0 && m.steps.Cmp(dumpHi) < 0 {
			hh := fnv.New64a()
			hh.Write([]byte(m.show()))
			fmt.Fprintf(dumpW, "%s %016x\n", m.steps.String(), hh.Sum64())
		}
		if m.accel {
			if m.pending == nil && m.tryRun() {
				m.hist = nil
				m.sample()
			} else {
				m.tryJump()
			}
		}
		if m.nsample&0xfff == 0 {
			dg := digits(m.steps)
			if dg >= lastReport+100 {
				lastReport = dg - dg%100
				fmt.Fprintf(os.Stderr, "progress: steps~1e%d events %d jumps %d runs %d births %d (mid-hop %d) triples %d len %d, %.0f s\n", dg-1, m.nsample, m.njump, m.nrun, nbirth, nmidhop, ntriple, n, time.Since(t0).Seconds())
			}
		}
		if m.steps.Cmp(limit) >= 0 && m.pending == nil {
			break
		}
	}
	st := m.steps.String()
	if len(st) > 60 && !full {
		st = fmt.Sprintf("%s..(%d digits)", st[:30], len(st))
	}
	fmt.Printf("steps %s events %d raw %d bulk %d jumps %d rollbacks %d runs %d (packs %d, unpacks %d)\n", st, m.nsample, m.nraw, m.nbulk, m.njump, m.nroll, m.nrun, m.npack, m.nunpack)
	fmt.Printf("births seen %d (mid-hop %d, other with cursors side by side %d); visits with 1 1: %d appearances; with 1 1 1: %d\n", nbirth, nmidhop, nother, npair, ntriple)
	sh := m.show()
	if !full {
		sh = abbreviate(sh)
		if len(sh) > 700 {
			sh = "..." + sh[len(sh)-700:]
		}
	}
	fmt.Println(sh)
}
