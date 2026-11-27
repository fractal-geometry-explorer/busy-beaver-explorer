import json
def b5(x):
    if x==0: return "0"
    s="";n=abs(x)
    while n: s=str(n%5)+s; n//=5
    return ("-" if x<0 else "")+s
def load(f): return [(int(s),[int(x) for x in l]) for s,l in map(json.loads,open(f))]
