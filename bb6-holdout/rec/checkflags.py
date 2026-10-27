"""Run every flagged GMM state from a gmmseg output file on the real machine (through the proven rules)."""
import sys
import hybsim
halts = []; n = 0; inval = 0
for line in open(sys.argv[1]):
    p = line.split()
    if len(p) < 7: continue
    m, E = int(p[0]), int(p[1])
    try:
        res = hybsim.run(hybsim.config_from([('G', 1), ('M', m), ('M', E - 2)], E), max_rounds=100000, log=lambda *a: None)
    except AssertionError:
        inval += 1; continue
    n += 1
    print(m, E, p[2:], res['result'], res.get('rule', ''), res['rounds'], flush=True)
    if res['result'] == 'halt': halts.append((m, E))
print(f"flagged states run on the real machine: {n} (invalid tapes {inval}); halting: {halts}")
