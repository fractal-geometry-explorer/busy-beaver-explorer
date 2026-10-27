import re, sys
log = open(sys.argv[1]).read().splitlines()
first = {}; last_open = None; lastk = None
for line in log:
    m = re.match(r"digits\s+(\d+): settled (\d+), still open (\d+).*chain counts:(.*)", line)
    if not m: continue
    k, op = int(m.group(1)), int(m.group(3)); lastk, last_open = k, op
    for kv in m.group(4).split():
        c, cnt = map(int, kv.split(":"))
        first.setdefault(c, k)
print("fewest digits that fix a chain of L meetings:", ", ".join(f"L={c}: {k}" for c, k in sorted(first.items())))
print(f"open after {lastk} digits: {last_open} classes = density {last_open / 2**lastk:.2e} of all n")
for line in log:
    if line.startswith("density"):
        parts = line.split(":", 1)[1].split()
        print("settled density by chain length:", " ".join(parts))
