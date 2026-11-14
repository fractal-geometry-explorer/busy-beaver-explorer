"""An independent evaluation of a jump: the zone as an odometer, V visits composed from single visits by doubling.
Coordinates N_0 = n_0 - b_1, N_j = n_j + b_j - b_{j+1} (b_{k+1} := 0).  A visit whose lowest 0 bit is b_i:
cost 6*(N_0+..+N_{i-1}) + 4i + 11 steps, then N_0 += 2, N_{i-1} -= 1, bits incremented."""
_E={}   # z -> (a list len z, c, d list len z) : 2^z-1 visits from low z bits 0: cost = sum a[j]*N[j] + c, N[j] += d[j] (j<z)
def E(z):
    if z in _E: return _E[z]
    if z==0: r=([],0,[])
    else:
        a,c,d=E(z-1)
        # first half
        a1=a+[0]; c1=c; d1=d+[0]
        # the visit with i=z: cost 6*sum_{j<z}(N_j+d1_j) + 4z+11 ; then N_0+=2, N_{z-1}-=1
        a2=[6]*z; c2=6*sum(d1)+4*z+11
        d2=list(d1); d2[0]+=2; d2[z-1]-=1
        # second half on shifted N
        c3=c+sum(x*y for x,y in zip(a,d2))
        r=([a1[j]+a2[j]+(a[j] if j<z-1 else 0) for j in range(z)], c1+c2+c3, [d2[j]+(d[j] if j<z-1 else 0) for j in range(z)])
    _E[z]=r; return r
def run(counts,bits,V):
    """counts [n_k..n_0], bits [b_k..b_1] as in m1acc; returns (counts, bits, steps) after V visits"""
    k=len(bits); n=counts[::-1]; b=[0]+bits[::-1]+[0]     # n[j], b[j] j=1..k
    N=[n[0]-b[1]]+[n[j]+b[j]-b[j+1] for j in range(1,k+1)]
    B=sum(b[j]<<(j-1) for j in range(1,k+1)); steps=0
    while V>0:
        z=0
        while z<k and (B>>z)&1==0 and (1<<(z+1))-1<=V and B&((1<<(z+1))-1)==0: z+=1
        if z>0:
            a,c,d=E(z); steps+=c+sum(a[j]*N[j] for j in range(z))
            for j in range(z): N[j]+=d[j]
            B+=(1<<z)-1; V-=(1<<z)-1
            if V==0: break
        i=1
        while (B>>(i-1))&1: i+=1
        assert i<=k
        steps+=6*sum(N[:i])+4*i+11; N[0]+=2; N[i-1]-=1; B+=1; V-=1
    b=[0]+[(B>>(j-1))&1 for j in range(1,k+1)]+[0]
    n=[N[0]+b[1]]+[N[j]-b[j]+b[j+1] for j in range(1,k+1)]
    return n[::-1],b[k:0:-1],steps
