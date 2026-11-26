import sys, random
W={'Z':'101010','O':'10','T':'100000','b1_2':'100','b2_1':'110','b1_4':'10000','b2_3':'11000'}
TOPS=[['b1_2'],['b2_1','T'],['b1_2','Z'],['b1_2','O'],['b1_4'],['b2_1','Z'],['b2_1','O'],['b2_3'],['b2_1']]
s=float(sys.argv[1]); n=int(sys.argv[2]); nd=int(sys.argv[3]); random.seed(int(sys.argv[4]))
for _ in range(n):
    top=random.choice(TOPS)
    out=''.join(W[x] for x in top)
    for j in range(nd):
        out+='1000'*random.randint(0,int(s*2**j))+W[random.choice('ZOT')]
    out+='1000'*random.randint(0,int(s*2**nd))+'100'
    print(out)
