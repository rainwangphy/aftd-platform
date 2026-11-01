import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# additive_valuation_bundle_last_cases

Topic: fair_division   Node: 1dd2820b0000

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01.

Assigning the additional last good to agent s adds exactly its value to the old bundle value of s and leaves every other bundle value unchanged.
-/

open Function Finset

theorem additive_valuation_bundle_last_cases {m n : ℕ} (u : Fin (m+1) → ℝ)
    (σ : Fin m → Fin n) (s j : Fin n) :
    additive_valuation u (bundle_of (Fin.lastCases s σ) j) =
      additive_valuation (fun g => u g.castSucc) (bundle_of σ j) +
        if s = j then u (Fin.last m) else 0 := by
  simp only [additive_valuation, bundle_of, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp
