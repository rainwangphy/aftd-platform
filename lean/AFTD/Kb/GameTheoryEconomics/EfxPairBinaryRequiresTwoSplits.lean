import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryValues
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryNoOneSplitAllocation
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods

/-!
# efx_pair_binary_requires_two_splits

Topic: fair_division   Node: 6b790513da65

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Exact route obstruction from experiment 10993, not a counterexample to EFX existence; no novelty claim.

Every complete EFX allocation of the explicit binary nine-good matrix cast to real values separates the two members of at least two distinct old adjacent pairs among goods 0 through 7.
-/

open Function Finset

theorem efx_pair_binary_requires_two_splits (σ : Fin 9 → Fin 4)
    (hσ : is_efx_goods (fun i g => (efx_pair_binary_values i g : ℝ)) σ) :
    ∃ a b : Fin 4, a ≠ b ∧
      σ (![0,2,4,6] a) ≠ σ (![1,3,5,7] a) ∧
      σ (![0,2,4,6] b) ≠ σ (![1,3,5,7] b) := by
  classical
  have h (r : Fin 4) : ∃ j : Fin 4, j ≠ r ∧ σ (![0,2,4,6] j) ≠ σ (![1,3,5,7] j) := by
    by_contra h
    push Not at h
    exact efx_pair_binary_no_one_split_allocation σ r h hσ
  obtain ⟨a, _, ha⟩ := h 0
  obtain ⟨b, hb, hbs⟩ := h a
  exact ⟨a, b, hb.symm, ha, hbs⟩
