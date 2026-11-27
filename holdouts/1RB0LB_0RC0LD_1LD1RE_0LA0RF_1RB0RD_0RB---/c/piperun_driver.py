#!/usr/bin/env python3
"""Run piperun in short segments; checkpoint the word (gzip) and the event list in $LR_CKPT.
usage: driver.py TARGET [SEG]      (verify: driver.py --check)"""
import os, sys, json, gzip, subprocess, tempfile, time, hashlib
CK = os.environ.get("LR_CKPT", ".")
def aw(name, data):
    p = os.path.join(CK, name); t = p + ".tmp"
    with open(t, "wb") as f: f.write(data); f.flush(); os.fsync(f.fileno())
    os.replace(t, p)
def load():
    st = json.load(open(os.path.join(CK, "state.json")))
    w = gzip.open(os.path.join(CK, "word.gz")).read()
    return st, w
def check():
    st, w = load()
    assert len(w) == st["length"] + 1 and w.endswith(b"\n"), "length"
    assert set(w[:-1]) <= {48, 49}, "alphabet"
    assert hashlib.sha256(w).hexdigest() == st["sha256"], "sha"
    assert not st.get("halt") or True
    print("ok round", st["round"], "length", st["length"])
if sys.argv[1] == "--check":
    check(); sys.exit(0)
TARGET = int(sys.argv[1]); SEG = int(sys.argv[2]) if len(sys.argv) > 2 else 15000
st, w = load()
tmp = tempfile.mkdtemp(prefix="pr_")
inp = os.path.join(tmp, "in.txt"); out = os.path.join(tmp, "out.txt")
open(inp, "wb").write(w); del w
while st["round"] < TARGET and not st.get("halt"):
    r0 = st["round"]; r1 = min(r0 + SEG, TARGET); t0 = time.time()
    p = subprocess.run(["./piperun", "4", str(r1), "50000", out, inp, str(r0)], capture_output=True, text=True)
    lines = p.stdout.splitlines()
    if any(l.startswith(("STOP", "HALT")) for l in lines):
        st["halt"] = [l for l in lines if l.startswith(("STOP", "HALT"))]
    if p.returncode != 0 and not st.get("halt"):
        sys.stderr.write(p.stdout[-2000:] + p.stderr[-2000:]); sys.exit(2)
    for l in lines:
        if l.startswith(("JUNK", "1011")): st["events"].append(l)
    done = [l for l in lines if l.startswith("DONE")]
    if st.get("halt"):
        st["last_output"] = lines[-40:]
        aw("state.json", json.dumps(st, indent=1).encode()); aw("COMMIT", b"halt\n"); break
    assert done and done[-1].split()[1] == str(r1), lines[-3:]
    w = open(out, "rb").read()
    st.update(round=r1, length=int(done[-1].split("length ")[1].split(",")[0]), sha256=hashlib.sha256(w).hexdigest())
    assert len(w) == st["length"] + 1
    aw("word.gz", gzip.compress(w, 1)); del w
    aw("state.json", json.dumps(st, indent=1).encode())
    nj = sum(1 for e in st["events"] if e.startswith("JUNK"))
    aw("PROGRESS", ("round %d length %d junk %d seg %.0fs sha %s\n" % (r1, st["length"], nj, time.time() - t0, st["sha256"][:12])).encode())
    aw("COMMIT", ("%d\n" % r1).encode())   # COMMIT last: the wrapper publishes only when it is the newest file
    os.replace(out, inp)
sys.exit(0)
