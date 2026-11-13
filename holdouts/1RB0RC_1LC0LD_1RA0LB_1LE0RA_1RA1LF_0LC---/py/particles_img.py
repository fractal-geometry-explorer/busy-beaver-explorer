# defect density image: rows = snapshots (snap output), x = position binned; dark = defect cells (t[i]==t[i+1])
import sys, base64, io
from PIL import Image
f, out, X0, X1, WPX = sys.argv[1], sys.argv[2], int(sys.argv[3]), int(sys.argv[4]), int(sys.argv[5])
rows = []
for line in open(f):
    a = line.split()
    if len(a) < 6: continue
    rows.append((int(a[0]), int(a[3]), a[5]))
H = len(rows); sc = (X1 - X0) / WPX
img = Image.new('L', (WPX, H), 255); px = img.load()
for j, (t, lo, s) in enumerate(rows):
    xl = int((lo - X0) / sc); xh = int((lo + len(s) - X0) / sc)
    for x in range(max(0, xl), min(WPX, xh)): px[x, j] = 228   # visited
    for i in range(len(s) - 1):
        if s[i] == s[i + 1]:
            x = int((lo + i - X0) / sc)
            if 0 <= x < WPX: px[x, j] = 0
img = img.convert('P', palette=Image.ADAPTIVE, colors=4)
img.save(out, optimize=True); print(H, rows[0][0], rows[-1][0])
