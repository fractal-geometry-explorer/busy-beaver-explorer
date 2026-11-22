import itertools
def step(w):  # w[0]=1 fixed boundary (the 10 defect side), cells 1..n
    return [1]+[w[j-1]^w[j] for j in range(1,len(w))]
bad=0
for n in range(1,15):
    b=n.bit_length(); P=1<<b
    rows={tuple([1]+[1 if (j&s)==j else 0 for j in range(1,n+1)]) for s in range(P)}
    cnt=0
    for W in itertools.product([0,1],repeat=n):
        w=[1]+list(W); reach=False
        for t in range(P+1):
            if all(w[1:]): reach=True;break
            w=step(w)
        # periodic check
        w0=[1]+list(W); w=w0
        for t in range(P): w=step(w)
        assert w==w0
        if reach!=(tuple([1]+list(W)) in rows): bad+=1
        cnt+=reach
    # first time from all-x
    w=[1]+[0]*n; t=0
    while not all(w[1:]): w=step(w); t+=1
    print(n,'reachable gaps',cnt,'of',2**n,'pascal rows',len(rows),'all-x first all-y at',t,'=2^b-1',P-1)
print('mismatches',bad)
