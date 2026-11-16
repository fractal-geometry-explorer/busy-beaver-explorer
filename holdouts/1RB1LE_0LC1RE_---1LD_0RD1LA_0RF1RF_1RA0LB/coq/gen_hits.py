# Generates the level-hit, level-halt and front lemmas of the Coq proof.
PASS = {2: "H", 4: "V", 7: "H", 10: "V", 12: "H", 15: "V"}
INC = {3, 7, 11, 15}
HALT = [(2,"H4","HC"),(2,"HC","HC"),(4,"HC","H4"),(7,"H4","HC"),(7,"HC","HC"),(10,"HC","HC"),(12,"H4","H4"),(12,"HC","H4"),(15,"HC","HC")]
kind = lambda p: "H" if p % 2 == 0 else "V"
out = []
for p in range(16):
    n = (p + 1) % 16
    j2 = "(S j)" if p in INC else "j"
    k = kind(p)
    if p in PASS:
        r = PASS[p]
        out.append(f"Lemma hit{p} j Y Y' : Hit{r} Y Y' -> Hit{k} (W {p} j Y) (W {n} {j2} Y').\n"
                   f"Proof. intros H; destruct_hit H; solve_hit. Qed.\n")
    else:
        out.append(f"Lemma hit{p} j Y : Hit{k} (W {p} j Y) (W {n} {j2} Y).\nProof. solve_hit. Qed.\n")
for p, a, b in HALT:
    out.append(f"Lemma halt{p}_{a} j Y : {a} Y -> {b} (W {p} j Y).\nProof. intros H; destruct_die H; solve_die. Qed.\n")
print("\n".join(out))
