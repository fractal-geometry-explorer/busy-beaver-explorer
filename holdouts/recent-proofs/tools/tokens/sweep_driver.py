#!/usr/bin/env python3
"""Run a list of tokgram tasks under the longrun wrapper (see /mnt/project-files/notes/long-runs.md).
Usage: sweep_driver.py TASKS WORKERS [--verify]
TASKS: one task per line: MACHINE L|R R CAP W J DEPTH T0 TL MAXNODES
State (longrun checkpoint, state.pkl): {"res": {task line: result line}}."""
import sys, os, subprocess, time, threading
import longrun
tasks = [l.strip() for l in open(sys.argv[1]) if l.strip()]
workers = int(sys.argv[2])
st = longrun.load(default={"res": {}})
if "--verify" in sys.argv:
    assert all(k in set(tasks) for k in st["res"]), "checkpoint has results for unknown tasks"
    print("verify ok: %d of %d" % (len(st["res"]), len(tasks))); sys.exit(0)
lock = threading.Lock(); todo = [t for t in tasks if t not in st["res"]]; pos = [0]
def run(t):
    m, o, r, cap, w, j, d, t0, tl, maxn = t.split()
    env = dict(os.environ, J=j, DEPTH=d, T0=t0, TL=tl, SEEDMAX="50000000")
    try:
        out = subprocess.run(["./tokgram", m, o, r, cap, w, maxn], env=env, capture_output=True, text=True, timeout=float(tl) * 3 + 120).stdout
    except subprocess.TimeoutExpired:
        out = "TIMEOUT"
    out = out.strip().split("\n")[-1] if out.strip() else "EMPTY"
    if ": " in out: out = out.split(": ", 1)[1]
    return out[:400]
def worker():
    while True:
        with lock:
            if pos[0] >= len(todo): return
            t = todo[pos[0]]; pos[0] += 1
        r = run(t)
        with lock: st["res"][t] = r
def save():
    with lock:
        n = len(st["res"]); closed = [k for k, v in st["res"].items() if v.startswith("NONHALT")]
        longrun.save(st, progress="%d of %d tasks, %d closed%s" % (n, len(tasks), len(closed), (": " + closed[0].split()[0]) if closed else ""))
th = [threading.Thread(target=worker) for _ in range(workers)]
for x in th: x.start()
last = time.time()
while any(x.is_alive() for x in th):
    time.sleep(5)
    if time.time() - last > 180: save(); last = time.time()
save()
print("FINAL %d tasks" % len(st["res"]))
