# abstract two-counter model of the 1RB1LA_1LC1RD_1LA0LC_1RE0RB_ family
def stack_value(S):
    """S = [a_1..a_k] bottom..top (sentinel excluded): E = sum 2^{P_i}, P_k=a_k, P_i = P_{i+1}+1+a_i"""
    E=0; P=-1
    for a in reversed(S):
        P=P+1+a; E+=1<<P
    return E
def value_stack(E):
    """inverse: zero-run lengths of binary E (top = lowest bit)"""
    S=[]; prev=-1; p=0
    bits=[i for i in range(E.bit_length()) if E>>i&1]
    out=[]
    prev=-1
    for b in bits: out.append(b-prev-1); prev=b
    return list(reversed(out))   # bottom..top
def R_to_F(R):
    """R list (front first) starting with 0, then Q=R[1:] front = top"""
    assert R[0]==0
    Q=R[1:]
    return stack_value(list(reversed(Q)))
def F_to_R(F):
    Q=list(reversed(value_stack(F)))
    return [0]+Q
