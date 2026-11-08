import AFTD.Prelude

/-!
# is_three_distant_convex

Topic: general_equilibrium   Node: ac5b82a6d583

Provenance: formalization of a published result. Source: arXiv:2611.07572 Def 1

A cooperative game v on a finite set of players is 3-distant convex if v(S) + v(T) ≤ v(S ∪ T) + v(S ∩ T) for all coalitions S and T whose symmetric difference has cardinality at least 3.
-/

/-- A cooperative game v on a finite set of players is 3-distant convex if the convexity condition holds for all pairs of coalitions whose symmetric difference has cardinality at least 3. -/
def is_three_distant_convex {α : Type*} [DecidableEq α] (v : Finset α → ℝ) : Prop := ∀ S T : Finset α, 3 ≤ (symmDiff S T).card → v S + v T ≤ v (S ∪ T) + v (S ∩ T)
