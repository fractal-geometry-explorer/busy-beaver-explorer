"""Parser of the machine text for laws.py / gen_visit.py."""
def parse(m):
    t={}
    for i,s in enumerate(m.split('_')):
        for r in range(2):
            x=s[3*r:3*r+3]
            if x[2]!='-': t[(i,r)]=(int(x[0]),1 if x[1]=='R' else -1,ord(x[2])-65)
    return t
