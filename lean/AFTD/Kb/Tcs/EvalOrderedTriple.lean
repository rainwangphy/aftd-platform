import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.OrderedTriple

/-!
# eval_ordered_triple

Topic: combinatorics   Node: 5863443b73cf

Provenance: formalization of a published result. Source: arXiv:2610.03808 Def. 6.1

Given a function chi : OrderedTriple α → ℤˣ assigning units of ℤ to ordered triples in a linearly ordered type α, and elements x, a, b : α with a < b, x ≠ a, and x ≠ b, eval_ordered_triple chi x a b hab hxa hxb evaluates chi at (x, a, b) by returning chi(x, a, b) if x < a, -chi(a, x, b) if a < x < b, and chi(a, b, x) if b < x.
-/

/-- Evaluation of a chirotope on an ordered triple of distinct elements, accounting for the sign of the sorting permutation. -/
def eval_ordered_triple {α : Type*} [LinearOrder α] (chi : OrderedTriple α → ℤˣ) (x a b : α) (hab : a < b) (hxa : x ≠ a) (hxb : x ≠ b) : ℤˣ :=
  if hx : x < a then
    chi ⟨x, a, b, hx, hab⟩
  else if hb : x < b then
    -chi ⟨a, x, b, lt_of_le_of_ne (not_lt.mp hx) hxa.symm, hb⟩
  else
    chi ⟨a, b, x, hab, lt_of_le_of_ne (not_lt.mp hb) hxb.symm⟩
