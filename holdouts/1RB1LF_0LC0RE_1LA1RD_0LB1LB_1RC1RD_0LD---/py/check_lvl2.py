"""check_lvl2.py MSIM JOBS [STEPS]: compare lvl2.py with the exact macro simulator msim (itself checked against the
direct simulator).  For every machine: run lvl2 to STEPS (it stops at the first macro-step boundary at or after
STEPS); then run msim to the step count lvl2 reports and compare state, head side and the whole run-length tape.
Also every tape-end record lvl2 prints must be a record of msim with the same tape."""
import subprocess, sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import lvl2
msim, jobs = sys.argv[1], sys.argv[2]; steps = int(sys.argv[3]) if len(sys.argv) > 3 else 10**10
bad = 0
for line in open(jobs):
    f = line.split()
    if not f: continue
    m, K = f[0], int(f[1]); recs = []
    def rec(s, fr):
        if fr == 1: recs.append("%d %s" % (s.steps, " ".join(s.show().split())))
    s, why, ms, nacc = lvl2.run(m, K, steps, rec=rec)
    out = subprocess.run([msim, m, str(K), str(s.steps)], capture_output=True, text=True).stdout.strip().split("\n")
    end = out[-1].split(" ", 2); want = "%d %s" % (s.steps, " ".join(s.show().split()))
    ok = end[0] == "END" and " ".join(end[2].split()) == want
    ref = set(" ".join(l.split()) for l in out[:-1])
    ok2 = all(r in ref for r in recs)
    print("%s K=%d steps=%d accel=%d records=%d/%d end:%s records:%s" % (m, K, s.steps, nacc, len(recs), len(ref), "ok" if ok else "DIFF", "ok" if ok2 else "DIFF"), flush=True)
    bad += (not ok) + (not ok2)
print("ALL CHECKS PASS" if not bad else "%d FAILURES" % bad)
