import AFTD.Prelude

/-!
# is_in_core

Topic: general_equilibrium   Node: df205b8a7f5a

Provenance: formalization of a published result. Source: arXiv:2611.16207, Section 2

An allocation x belongs to the core of a cooperative game v on finite player set α if the total payoff equals v(univ) and every coalition S receives at least v(S).
-/

/-- An allocation belongs to the core of a cooperative game if it is efficient and coalitionally rational. -/
def is_in_core {α : Type*} [Fintype α] (v : Finset α → ℝ) (x : α → ℝ) : Prop :=
  (∑ i, x i = v Finset.univ) ∧ ∀ S : Finset α, v S ≤ ∑ i ∈ S, x i
