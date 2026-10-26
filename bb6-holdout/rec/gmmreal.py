"""Every GMM round start (gap at 1, marker at m, end marker at E - 2) of width E in a range, on the real machine
through the proven rules (fallback to plain transitions at contacts): does any halt?"""
import sys, time
import hybsim
Emin, Emax = int(sys.argv[1]), int(sys.argv[2])
cnt = halts = other = contacts = 0; t0 = time.time()
for E in range(Emin, Emax + 1):
    if E % 2 == 0: continue
    for m in range(6, E - 7, 2):
        cnt += 1
        res = hybsim.run(hybsim.config_from([('G', 1), ('M', m), ('M', E - 2)], E), max_rounds=100000, log=lambda *a: None)
        if res['result'] == 'halt': halts += 1; print("HALT", m, E, res['steps'], flush=True)
        elif res['result'] != 'clean': other += 1; print("OTHER", m, E, res['result'], flush=True)
        if res.get('contacts'): contacts += 1
print(f"{cnt} GMM states with width {Emin}..{Emax}: {halts} halt, {other} other, {contacts} needed plain transitions ({time.time() - t0:.0f} s)")
