import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.EvalOrderedTriple
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.OrderedTriple

/-!
# is_rank_three_uniform_chirotope

Topic: combinatorics   Node: 9988cd3e5587

Provenance: formalization of a published result. Source: arXiv:2610.03808 Def. 6.1

A function chi : OrderedTriple α → ℤˣ assigning units of ℤ to ordered triples in a linearly ordered type α is a uniform rank-3 chirotope if for every x : α and every sorted 4-set a < b < c < d in α disjoint from x, the three terms of the 3-term Grassmann-Plücker relation evaluated using eval_ordered_triple are not all equal.
-/

/-- Grassmann-Plücker 3-term condition for uniform rank-3 chirotopes. -/
def is_rank_three_uniform_chirotope {α : Type*} [LinearOrder α] (chi : OrderedTriple α → ℤˣ) : Prop :=
  ∀ (x a b c d : α) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hxa : x ≠ a) (hxb : x ≠ b) (hxc : x ≠ c) (hxd : x ≠ d),
    let t₁ := eval_ordered_triple chi x a b hab hxa hxb * eval_ordered_triple chi x c d hcd hxc hxd
    let t₂ := -(eval_ordered_triple chi x a c (hab.trans hbc) hxa hxc * eval_ordered_triple chi x b d (hbc.trans hcd) hxb hxd)
    let t₃ := eval_ordered_triple chi x a d ((hab.trans hbc).trans hcd) hxa hxd * eval_ordered_triple chi x b c hbc hxb hxc
    ¬ (t₁ = t₂ ∧ t₂ = t₃)
