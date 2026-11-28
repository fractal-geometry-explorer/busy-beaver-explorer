package main

// cf.go: the counterfactual at a triple.  At a visit with three cursor cells 1 side by side (`0 a 1 1 1 a^10 Q b a^M 0
// B>`, the third 1 the active cursor) the run goes on only because the end block a^M is not empty.  runCF builds the
// tape that the visit would have left if the end block had been used up at exactly this visit (a birth: the last
// separator becomes a new cursor, `Q 0 a 1 B>`, and the triple is left standing) and runs it until the first cursor
// reaches the triple: it halts if that cursor is a 0 and the cells left of the triple are right (`b a 0 a 1 1 1`, see
// py/haltq.py left); otherwise the triple is destroyed: a cursor arrives without a halt, or every cursor right of the
// triple is used up so that the triple itself becomes the active cursor.  The tape right of the triple works like a
// run of its own until then, so this says whether the coincidence would have been enough for a halt.

import (
	"fmt"
	"math/big"
)

func tripleAt(L []Item) int {
	for i := 0; i+2 < len(L); i++ {
		if L[i].k == I1 && L[i+1].k == I1 && L[i+2].k == I1 {
			return i
		}
	}
	return -1
}

// runCF: L is the tape at the triple visit, ending with SS(M,1) I0.  Returns "HALT", "destroyed (a cursor arrives)",
// "destroyed (no cursor arrives)" or "open".
func runCF(L []Item, steps *big.Int, maxEv int64) (string, int64, *big.Int, string) {
	n := len(L)
	s := NewSim()
	s.L = append(append([]Item(nil), L[:n-2]...), Item{k: I0}, Item{k: W01, n: one}, Item{k: I1})
	s.s = sB
	s.steps = new(big.Int).Set(steps)
	start := new(big.Int).Set(steps)
	s.canon(0)
	var ev int64
	prev := s.L
	for ev < maxEv {
		if !s.event() {
			if s.pending != nil {
				s.rollback()
				continue
			}
			return "HALT", ev, sub(s.steps, start), ""
		}
		ev++
		s.sample()
		s.checkPending()
		if s.pending == nil {
			if tripleAt(s.L) < 0 {
				sh := abbreviate(s.show())
				if len(sh) > 300 {
					sh = sh[:300]
				}
				// cursors right of the triple at the last visit before (the end cell 0 not counted)
				how := "destroyed (no cursor arrives)"
				j := tripleAt(prev)
				for i := j + 3; i < len(prev)-1; i++ {
					if isInt(prev[i]) {
						how = "destroyed (a cursor arrives)"
					}
				}
				return how, ev, sub(s.steps, start), sh
			}
			prev = append([]Item(nil), s.L...)
		}
		if s.accel {
			if s.pending == nil && s.tryRun() {
				s.hist = nil
				s.sample()
			} else {
				s.tryJump()
			}
		}
	}
	return "open", ev, sub(s.steps, start), ""
}

func reportCF(ntriple int64, L []Item, steps *big.Int) {
	r, ev, ds, sh := runCF(L, steps, 200000000)
	fmt.Printf("CF triple=%d: %s after %d visits stopped at, %d-digit step count more (%s) | %s\n", ntriple, r, ev, digits(ds), abbreviate(ds.String()), sh)
}
