import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMatroidRankValuation
import AFTD.Kb.GameTheoryEconomics.HasBinaryMarginals
import AFTD.Kb.GameTheoryEconomics.IsSubmodular

/-!
# zero_is_matroid_rank_valuation

Topic: fair_division   Node: 2b605ea299a5

Provenance: helper lemma. folklore

The constantly zero set function is a matroid-rank valuation.
-/

/-- The zero valuation is a matroid-rank valuation. -/
theorem zero_is_matroid_rank_valuation (m : ℕ) :
    is_matroid_rank_valuation (fun (_ : Finset (Fin m)) => (0 : ℝ)) := by
  simp [is_matroid_rank_valuation, is_submodular, has_binary_marginals]
