"""The step families of the walk that gen_fam.py proves: (name, suffix, header index, digit runs top to bottom).
Names: step_<suffix>h<5|7 for the header 0110101|0110111>_<family>."""
FAMS = []
for st, suf, hi in (("1001h5", "1001", 0), ("1001h7", "1001", 1), ("11h7", "11", 1)):
    FAMS += [
        (f"step_{st}_oo", suf, hi, "0:1,0:1,1:2*r+5"),     # 0 0 1^(odd >= 5) -> 000
        (f"step_{st}_e0", suf, hi, "0:1,0:1,1:2*r+4"),     # 0 0 1^(even >= 4) -> 0000
        (f"step_{st}_e1", suf, hi, "1:1,0:1,1:2*r+4"),     # 1 0 1^(even >= 4) -> 1000
        (f"step_{st}_o0", suf, hi, "0:1,1:1,0:1,1:2*r+5"), # 0 1 0 1^(odd >= 5) -> 0000
        (f"step_{st}_o1", suf, hi, "1:1,1:1,0:1,1:2*r+5"), # 1 1 0 1^(odd >= 5) -> 1000
        (f"step_{st}_00", suf, hi, "0:2"),
        (f"step_{st}_10", suf, hi, "1:1,0:1"),
        (f"step_{st}_001", suf, hi, "0:2,1:1"),
        (f"step_{st}_0011", suf, hi, "0:2,1:2"),
        (f"step_{st}_1011", suf, hi, "1:1,0:1,1:2"),
        (f"step_{st}_0101", suf, hi, "0:1,1:1,0:1,1:1"),
        (f"step_{st}_1101", suf, hi, "1:2,0:1,1:1"),
        (f"step_{st}_00111", suf, hi, "0:2,1:3"),
        (f"step_{st}_010111", suf, hi, "0:1,1:1,0:1,1:3"),
        (f"step_{st}_110111", suf, hi, "1:2,0:1,1:3"),
    ]
for st, suf, hi in (("1h5", "1", 0), ("001h7", "001", 1)):
    FAMS += [
        (f"step_{st}_e", suf, hi, "0:1,1:1,0:2*r+2"),        # 0 1 0^(even >= 2) -> 000
        (f"step_{st}_o0", suf, hi, "0:1,1:1,0:2*r+3"),       # 0 1 0^(odd >= 3) -> 0000
        (f"step_{st}_o1", suf, hi, "1:2,0:2*r+3"),           # 1 1 0^(odd >= 3) -> 1000
        (f"step_{st}_e0", suf, hi, "0:1,1:2,0:2*r+2"),       # 0 1 1 0^(even >= 2) -> 0000
        (f"step_{st}_e1", suf, hi, "1:3,0:2*r+2"),           # 1 1 1 0^(even >= 2) -> 1000
        (f"step_{st}_01", suf, hi, "0:1,1:1"),
        (f"step_{st}_010", suf, hi, "0:1,1:1,0:1"),
        (f"step_{st}_110", suf, hi, "1:2,0:1"),
        (f"step_{st}_011", suf, hi, "0:1,1:2"),
        (f"step_{st}_111", suf, hi, "1:3"),
    ]
