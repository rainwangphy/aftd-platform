import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular
import AFTD.Kb.GameTheoryEconomics.HasBinaryMarginals

/-!
# is_matroid_rank_valuation

Topic: fair_division   Node: c86c017d464d

Provenance: formalization of a published result. Source: arXiv:2012.12710

A set function on a finite set of indivisible goods is a matroid-rank valuation if it evaluates the empty set to 0, is submodular, and has binary marginal gains (every marginal value is 0 or 1).
-/

/-- A matroid-rank valuation is a normalized, submodular set function with binary marginal gains. -/
def is_matroid_rank_valuation {m : ℕ} (v : Finset (Fin m) → ℝ) : Prop :=
  v ∅ = 0 ∧ is_submodular v ∧ has_binary_marginals v
