import Return

/-! The plan for the kernel check of the return map below 2^62 (`return62.py`): a cover of the class `a = 5 + 4u`
by subclasses, each small enough for one kernel `decide`.  Not part of any proof: it only picks the pieces. -/

namespace BB6d

/-- Symbolic passes made by `srun`. -/
def srunLen : Nat → List Aff → Nat
  | 0, _ => 0
  | f + 1, l => match snext l with
    | .ok l' => if isRet l' then 1 else srunLen f l' + 1
    | _ => 1

/-- Concrete passes made by `crun`. -/
def crunLen : Nat → List Nat → Nat
  | 0, _ => 0
  | f + 1, l => match next l with
    | .ok [b, a] => if b = 2 * a + 1 then 1 else crunLen f [b, a] + 1
    | .ok l' => crunLen f l' + 1
    | _ => 1

/-- The passes `explore` makes (concrete ones counted double). -/
def cost (B : Nat) : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | f + 1, d, p, q =>
    if B ≤ p then 0 else
    let c := srunLen 200 [⟨2 * p + 1, 2 * q⟩, ⟨p, q⟩]
    let cc := 2 * crunLen 1000 [2 * p + 1, p]
    match sgood p q with
    | .ok _ => c
    | .split => match d with
      | 0 => c + cc
      | d + 1 => c + cost B f d p (2 * q) + cost B f d (p + q) (2 * q)
    | .small => c + cc + cost B f d (p + q) q
    | .bad => c

inductive Plan where
  | leaf (d p q c : Nat)
  | node (l r : Plan)

/-- Split `p + q u` (depth `d` left) into halves until each piece costs at most `budget`; with the cost. -/
def plan (B budget : Nat) : Nat → Nat → Nat → Nat → Plan × Nat
  | 0, d, p, q => (.leaf d p q 0, 0)
  | f + 1, d, p, q =>
    let whole := fun (_ : Unit) => let c := cost B 200 d p q; (Plan.leaf d p q c, c)
    if B ≤ p then whole () else
    match sgood p q, d with
    | .ok _, _ => whole ()
    | _, 0 => whole ()
    | _, d + 1 =>
      let (l, cl) := plan B budget f d p (2 * q)
      let (r, cr) := plan B budget f d (p + q) (2 * q)
      if cl + cr ≤ budget then whole () else (.node l r, cl + cr)

def Plan.show : Plan → String
  | .leaf d p q c => s!"L {d} {p} {q} {c}"
  | .node l r => s!"N\n{l.show}\n{r.show}"

end BB6d
