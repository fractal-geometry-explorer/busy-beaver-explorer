import re, sys, math
rows = re.findall(r"closest approach to halting with (\d+) digits: ([\d.]+) halvings \(n = (\d+), distance (\d+)\); classes with a constant closest distance: (\d+)", open(sys.argv[1]).read())
print(" digits  best halvings  needed to halt  still short   n")
for d, h, n, md, cst in rows:
    d = int(d); n = int(n); md = int(md); need = math.log2((2 * n + 6) / 2)
    if d >= 16: print(f"  {d:2d}      {float(h):6.2f}         {need:5.2f}         {math.log2(md / 2):5.2f}     {n}")
print("classes with a constant closest distance:", sum(int(r[4]) for r in rows))
