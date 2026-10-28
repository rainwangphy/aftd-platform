import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMatroidRankValuation
import AFTD.Kb.GameTheoryEconomics.HasBinaryMarginals
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# empty_eq_zero_of_matroid_rank_valuation

Topic: fair_division   Node: af76bb32f426

Provenance: helper lemma. arXiv:2012.12710

A matroid-rank valuation evaluates the empty set to 0.
-/

/-- A matroid-rank valuation evaluates the empty set to 0. -/
theorem empty_eq_zero_of_matroid_rank_valuation {m : ℕ} {v : Finset (Fin m) → ℝ}
    (h : is_matroid_rank_valuation v) : v ∅ = 0 :=
  h.1
