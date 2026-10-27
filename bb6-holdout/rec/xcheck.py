import sys, time, casesim
casesim.CROSSCHECK = True
t0 = time.time()
rounds, cleans = casesim.run_from_blank(int(sys.argv[1]))
print("crosscheck ok:", len(rounds), "rounds,", len(cleans), "clean tapes,", round(time.time() - t0, 1), "s")
