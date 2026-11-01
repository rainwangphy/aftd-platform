import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryValues
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# efx_pair_binary_partial_value

Topic: fair_division   Node: 38a68a61f0ea

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Exact route obstruction from experiment 10993, not a counterexample to EFX existence; no novelty claim.

In the explicit binary instance, restrict to the first eight goods and assign the adjacent pairs to the four agents in order. Every agent values every assigned bundle at exactly 3.
-/

open Function Finset

theorem efx_pair_binary_partial_value : ∀ i j : Fin 4,
    additive_valuation (fun g : Fin 8 => (efx_pair_binary_values i g.castSucc : ℝ))
      (bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3] j) = 3 := by
  intro i j
  dsimp [additive_valuation]
  exact_mod_cast ((by decide +kernel : ∀ i j : Fin 4,
    (∑ g ∈ bundle_of ![(0 : Fin 4),0,1,1,2,2,3,3] j, efx_pair_binary_values i g.castSucc) = 3) i j)
