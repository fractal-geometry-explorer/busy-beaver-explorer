Trusted (C++/Python) tools used for the levels above the first left-end event. Not part of any Lean proof.

  sim.py, run1.py, ev.py  direct simulation of one "carry into L" event (ev.event(L, m, n): L, all-ones counter of
                          m units, wall n; returns the next phase-R configuration)
  acc.cpp                 hierarchical memoized iteration of the event map on L (g++ -O2 -o acc acc.cpp);
                          `ODD=1 ./acc 8 < Lp24.txt` iterates odd-counter events on L1 until a special (S) event;
                          `JUMP=1 ./acc 8 < P2.txt` iterates the jump map J on a P region; MEMCAP=<bytes> bounds memory
  jmap.py                 jump(P, "100000010111", nb=2): one jump into P, direct simulation (the reference for acc JUMP)
  chain.py                J-iteration, then the S event, then the next P (python3 chain.py P3.txt 3)
  Lp24.txt                L1 = P (1^9 0 1 0)^24 Q, the left part after S1
  L1end.txt               L just before S2 (after 2,266,846,918 events)
  P2.txt, P2end.txt       P after S2 (406 cells), and after 170,793,835 jumps, just before S3 (446 cells)
  P3.txt                  P after S3 (460 cells)
  P4.txt                  P after S4 (500 cells), after 2,048,289,505 jumps on P3
