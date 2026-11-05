import sys
from pullback import preds, shape
def origins(b, W, R, depth=0):
    """list of possible roots: ('entry',...) or chains through valid predecessors"""
    res = []
    if W <= 32*R: res.append(['entry'])
    for p in preds(b, W, R):
        k, E, R0, b0, st = p[:5]; a1 = p[5] if len(p) > 5 else None
        if st != 'ok': continue
        if a1 is None or a1 % 2 == 0 or a1 < 449 or b < a1 + 448: continue
        if k == 'half':
            if E <= 32*R0: res.append([f'half<-entry(E={E},R={R0},b={b0},a1={a1})'])
            continue
        for sub in origins(b0, E, R0, depth+1):
            res.append([f'{k}<-(E={E},R={R0},b={b0},a1={a1})'] + sub)
    return res
def main():
  pass
if __name__ == "__main__":
 for line in open(sys.argv[1]):
     f = line.rstrip('\n').split('\t')
     R, b, W = int(f[2]), int(f[3]), int(f[4])
     if W % 6 != 2: continue
     o = origins(b, W, R)
     kinds = sorted(set(' / '.join(x[:1]) .split('<-')[0] for x in o))
     print(f[0], f[1], f'R/W={f[5]} D/W={f[6]}', f[9], '|', len(o), 'origins:', kinds)
     for x in o:
         if x != ['entry']: print('     ', ' '.join(x))
