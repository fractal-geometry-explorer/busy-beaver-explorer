#!/usr/bin/env python3
"""Independent check of py/closure/cert.json with the tools of this folder (accel.cpp, plain.cpp).
Reads from the certificate only: tail, r, m, r0, to, k, c, steps, start, thr.   Usage: see README.md."""
import json, sys, os, random, subprocess, math, time
HERE = os.path.dirname(os.path.abspath(__file__))
M = "1RB0RD_1RC0LF_1LA0LB_---1RE_1LB1RA_0LC0RA"
BIN = os.environ.get("VBIN", "/tmp/claude-0/g09/verify11019")
cert = json.load(open(os.path.join(HERE, "..", "py", "closure", "cert.json")))
CL = cert["classes"]; THR = cert["thr"]
assert cert["machine"] == M and cert["prefix"] == "01001000" and cert["word"] == "01"
index = {(c["tail"], c["m"], c["r"]): c for c in CL}
tailmod = {}
for c in CL: tailmod.setdefault(c["tail"], set()).add(c["m"])

def accel(lines, opts=()):
    p = subprocess.run([os.path.join(BIN, "accel"), *opts, M], input="\n".join(lines) + "\n", capture_output=True, text=True)
    assert p.returncode == 0, p.stderr
    res, cur = [], []
    for l in p.stdout.splitlines():
        if l.startswith("#"): res.append((cur, l)); cur = []
        else: cur.append(l)
    assert len(res) == len(lines), (len(res), len(lines))
    return res

def plain(lines, maxsteps, minB=0):
    p = subprocess.run([os.path.join(BIN, "plain"), M, str(maxsteps), str(minB)], input="\n".join(lines) + "\n", capture_output=True, text=True)
    assert p.returncode == 0
    return p.stdout.splitlines()

def in_set(T, B):
    """is (T, B) a member of a listed class?"""
    if B < THR or T not in tailmod: return False
    return any((T, m, B % m) in index for m in tailmod[T])

def static():
    """the certificate as a table: well-formed, and closed as a table (every successor residue is listed)"""
    bad = 0
    assert len(index) == len(CL), "duplicate classes"
    for t, ms in tailmod.items():
        if len(ms) != 1: print("tail with several moduli", t, ms); bad += 1
    for c in CL:
        if c["kind"] != "node": print("kind", c["kind"]); bad += 1
        r0 = c["r0"]
        if not (r0 >= THR and r0 % c["m"] == c["r"] and r0 - c["m"] < THR): print("r0 wrong", c["tail"], c["r"]); bad += 1
        if c["k"] < THR or c["c"] <= 0: print("k/c", c["k"], c["c"]); bad += 1
        to = c["to"]
        if to not in tailmod: print("successor tail not listed", to); bad += 1; continue
        for m2 in tailmod[to]:
            g = math.gcd(c["c"], m2)
            for j in range(m2 // g):
                if (to, m2, (c["k"] + c["c"] * j) % m2) not in index: print("successor residue not listed", to[:30], m2, (c["k"] + c["c"] * j) % m2); bad += 1
    s = cert["start"]
    if not in_set(s["tail"], s["B"]): print("start not in the set"); bad += 1
    from collections import Counter
    print("static: classes", len(CL), "tails", len(tailmod), "moduli", dict(Counter(c["m"] for c in CL)),
          "growth", dict(Counter((c["m"], c["c"]) for c in CL)), "least k", min(c["k"] for c in CL), "problems", bad)
    return bad

def expect(c, x):
    s = [int(v) for v in c["steps"]]
    return s[0] + s[1] * x + s[2] * x * x, c["k"] + c["c"] * x, c["to"]

def run_members(members, opts=(), label=""):
    """members: list of (class, x).  Returns number of mismatches."""
    lines = ["%d %s" % (c["r0"] + c["m"] * x, c["tail"]) for c, x in members]
    t0 = time.time(); res = accel(lines, opts); bad = 0; jumps = 0
    for (c, x), (out, stat) in zip(members, res):
        st, B2, T2 = expect(c, x)
        want = "NODE %d %d %s" % (st, B2, T2)
        jumps += int(stat.split("jumps=")[1].split()[0])
        if out != [want] or not in_set(T2, B2):
            bad += 1
            print("MISMATCH class tail=%s r=%d m=%d x=%d B=%d\n  got  %s\n  want %s  in_set=%s" % (c["tail"], c["r"], c["m"], x, c["r0"] + c["m"] * x, [o[:200] for o in out], want[:200], in_set(T2, B2)))
    print("%s: %d members run, %d mismatches, %d cycle jumps, %.1f s (opts %s)" % (label, len(members), bad, jumps, time.time() - t0, " ".join(opts) or "default"))
    return bad

def main():
    cmd = sys.argv[1]
    if cmd == "static":
        sys.exit(1 if static() else 0)
    if cmd == "classes":      # every class: x = 0, 1, one with B about 10^6..10^7, one with B about 10^12
        rnd = random.Random(11019); mem = []
        for c in CL:
            mem += [(c, 0), (c, 1), (c, rnd.randrange(10**6, 10**7) // c["m"]), (c, rnd.randrange(10**11, 10**12) // c["m"])]
        opts = tuple(sys.argv[2:])
        sys.exit(1 if run_members(mem, opts, "classes (4 members each)") else 0)
    if cmd == "nojump":       # every class at x = 0 and x = 1 with the cycle jumps switched off (chain steps only)
        mem = [(c, x) for c in CL for x in (0, 1)]
        sys.exit(1 if run_members(mem, ("-nojump",), "classes, x = 0 and 1, no cycle jumps") else 0)
    if cmd == "real":         # follow the real run from the start node, round by round, while B < 10^17
        s = cert["start"]; T, B = s["tail"], s["B"]; total = s["steps"]; n = 0; bad = 0; used = set()
        while B < 10**17:
            m = next(iter(tailmod[T])); c = index[(T, m, B % m)]; x = (B - c["r0"]) // m; st, B2, T2 = expect(c, x)
            out = accel(["%d %s" % (B, T)])[0][0]
            if out != ["NODE %d %d %s" % (st, B2, T2)] or not in_set(T2, B2): bad += 1; print("MISMATCH at round", n, B, T, out); break
            used.add((T, m, B % m)); T, B = T2, B2; total += st; n += 1
        print("real: %d consecutive rounds from the start node (B %d -> %d, step %d), classes used %d, mismatches %d" % (n, s["B"], B, total, len(used), bad))
        sys.exit(1 if bad else 0)
    if cmd == "selftest":     # the comparison is not vacuous: a certificate with k + 1, or steps + 1, or another tail must fail
        import copy, io, contextlib
        rnd = random.Random(5); caught = 0; tries = 0
        for field in ("k", "c", "steps0", "steps1", "steps2", "to"):
            for _ in range(5):
                c = copy.deepcopy(rnd.choice(CL))
                if field in ("k", "c"): c[field] += 1
                elif field == "to": c["to"] = rnd.choice([t for t in tailmod if t != c["to"]])
                else: i = int(field[-1]); c["steps"][i] = str(int(c["steps"][i]) + 1)
                buf = io.StringIO()
                with contextlib.redirect_stdout(buf): b = run_members([(c, 0), (c, 1), (c, 54321)])
                tries += 1; caught += b > 0
        print("selftest: %d altered classes, %d reported" % (tries, caught))
        sys.exit(0 if caught == tries else 1)
    if cmd == "random":       # N random (class, B <= 10^9)
        n = int(sys.argv[2]); rnd = random.Random(int(sys.argv[3])); mem = []
        for _ in range(n):
            c = rnd.choice(CL); B = rnd.randrange(THR, 10**9); mem.append((c, (B - c["r0"]) // c["m"] if B >= c["r0"] else 0))
        sys.exit(1 if run_members(mem, tuple(sys.argv[4:]), "random members, B < 10^9") else 0)
    if cmd == "small":        # N small x (0..199): dense in x near the threshold
        n = int(sys.argv[2]); rnd = random.Random(int(sys.argv[3])); mem = [(rnd.choice(CL), rnd.randrange(2, 200)) for _ in range(n)]
        sys.exit(1 if run_members(mem, tuple(sys.argv[4:]), "random members, x < 200") else 0)
    if cmd == "diff":         # accel against plain on small tapes: tails of the set and mutated tails, B small
        n = int(sys.argv[2]); rnd = random.Random(int(sys.argv[3])); lo, hi = int(sys.argv[4]), int(sys.argv[5]); maxsteps = int(sys.argv[6])
        tails = sorted(tailmod); lines = []
        for _ in range(n):
            t = rnd.choice(tails); mode = rnd.randrange(4)
            if mode == 1:      # lengthen or shorten one (10) block by a pair
                i = rnd.randrange(len(t) - 1)
                j = t.find("10", i)
                if j >= 0: t = t[:j] + ("1010" if rnd.random() < .5 else "") + t[j + 2:]
            elif mode == 2:    # flip one cell
                i = rnd.randrange(len(t)); t = t[:i] + ("1" if t[i] == "0" else "0") + t[i + 1:]
            elif mode == 3:    # random short tail
                t = "".join(rnd.choice("01") for _ in range(rnd.randrange(1, 40)))
            t = t.rstrip("0") or "-"
            lines.append("%d %s" % (rnd.randrange(lo, hi), t))
        pl = plain(lines, maxsteps); bad = 0; kinds = {}
        for opts in (("-nojump",), (), ("-big", "4"), ("-K", "12", "-big", "5"), ("-K", "2", "-big", "9"), ("-K", "4", "-big", "6"), ("-K", "8", "-big", "4"), ("-K", "18")):
            res = accel(lines, opts); jumps = 0
            flat = [o for out, _ in res for o in out]
            for out, stat in res: jumps += int(stat.split("jumps=")[1].split()[0])
            if flat != pl:
                bad += 1
                for i, (a, b) in enumerate(zip(flat, pl)):
                    if a != b: print("DIFF", opts, "\n ", lines[i][:100], "\n  accel", a[:150], "\n  plain", b[:150]); break
            print("  opts %-16s %d inputs, agrees with plain: %s, cycle jumps %d" % (" ".join(opts) or "default", len(lines), flat == pl, jumps))
        for l in pl: kinds[l.split()[0]] = kinds.get(l.split()[0], 0) + 1
        print("diff: %d inputs (B in [%d,%d)), plain outcomes %s, option sets disagreeing: %d" % (n, lo, hi, kinds, bad))
        sys.exit(1 if bad else 0)
    if cmd == "plainclass":   # N random classes at x = X: plain simulation against the certificate and accel
        n = int(sys.argv[2]); rnd = random.Random(int(sys.argv[3])); x = int(sys.argv[4]); bad = 0
        for _ in range(n):
            c = rnd.choice(CL); B = c["r0"] + c["m"] * x; st, B2, T2 = expect(c, x); want = "NODE %d %d %s" % (st, B2, T2)
            line = "%d %s" % (B, c["tail"]); t0 = time.time()
            pl = plain([line], st + 1000); ac = accel([line])[0][0]
            ok = pl == [want] and ac == [want]; bad += not ok
            print("  tail %s.. r=%d m=%d B=%d: plain %s, %d steps, %s (%.0f s)" % (c["tail"][:24], c["r"], c["m"], B, pl[0][:30], st, "OK" if ok else "MISMATCH", time.time() - t0), flush=True)
        print("plainclass: %d classes at x=%d against plain simulation, mismatches %d" % (n, x, bad))
        sys.exit(1 if bad else 0)
    if cmd == "halting":      # the five neighbouring tails of the notes: halt for B = 20002 + 3x ?
        tails = [l.split("tail ")[1].split(",")[0] for l in open(sys.argv[2]) if "HALTS for every" in l]
        steps = [l.split("steps ")[1].strip() for l in open(sys.argv[2]) if "HALTS for every" in l]
        bad = 0
        for t, sdesc in zip(tails, steps):
            a, b = sdesc.split("+"); a = int(a); b = int(b.split("*")[0])
            xs = [0, 1, 3, 1000, 333333, 10**8]
            res = accel(["%d %s" % (20002 + 3 * x, t) for x in xs])
            got = [o[0] for o, _ in res]; want = ["HALT %d" % (a + b * x) for x in xs]
            pl = plain(["%d %s" % (20002 + 3 * x, t) for x in xs[:3]], 10**9)
            ok = got == want and pl == want[:3]; bad += not ok
            print("  tail %s..(%d cells) in set: %s; accel at x=%s: %s; plain at x=0,1,3: %s; notes: %s  -> %s" % (t[:20], len(t), t in tailmod, xs, got, pl, sdesc, "OK" if ok else "MISMATCH"))
            # random B = 1 mod 3
        print("halting: %d tails, mismatches %d" % (len(tails), bad))
        sys.exit(1 if bad else 0)
main()
