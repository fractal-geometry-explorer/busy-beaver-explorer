"""Build c/rsim_events (an event-printing variant of the shared accelerated simulator) and run it.

The shared simulator holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/c/rsim.cpp is copied with one hook added:
whenever the tape grows at the left end, the step count, the state and the whole tape (ropes of words with counts)
are printed.  Its sample-level jumps are validated against direct simulation but not proved (see that file).

usage: python3 py/rsim_events.py MAXSTEPS > events.txt     then   python3 py/drain_ends.py events.txt"""
import os, subprocess, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.join(HERE, "../../..")
SRC = os.path.join(ROOT, "holdouts/1RB0LC_1RC1RA_1LD0RE_1LA1LD_0RA1RF_0LC---/c/rsim.cpp")
OUT = os.path.join(HERE, "../c/rsim_events")
M = os.path.basename(os.path.dirname(HERE))

s = open(SRC).read()
s = s.replace("""        if (rope.empty()) {
            if (d < 0) { buf.insert""", """        if (rope.empty()) {
            if (d < 0) { if (evmode) printf("L %s %c %s\\n", dec(steps).c_str(), 'A' + s, tape_dump().c_str()); buf.insert""", 1)
s = s.replace("    void run(I maxsteps) {", "    bool evmode = false;\n    void run(I maxsteps) {", 1)
s = s.replace("    I mx = parse_num(argv[2]);", """    if (mode == "events") {
        sim.evmode = true; I mx = parse_num(argv[3]);
        try { sim.run(mx); printf("running %s\\n", dec(sim.steps).c_str()); }
        catch (Halt &) { printf("halted %s\\n", dec(sim.steps).c_str()); }
        catch (Overflow &) { printf("OVERFLOW at %s\\n", dec(sim.steps).c_str()); }
        return 0;
    }
    I mx = parse_num(argv[2]);""", 1)
assert s.count("evmode") >= 3
open(OUT + ".cpp", "w").write(s)
subprocess.run(["g++", "-O2", "-o", OUT, OUT + ".cpp"], check=True)
os.remove(OUT + ".cpp")
sys.stdout.flush()
subprocess.run([OUT, M, "events", sys.argv[1] if len(sys.argv) > 1 else "1e14"], check=True)
