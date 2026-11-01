import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryValues
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryOneSplit
import AFTD.Kb.GameTheoryEconomics.EfxPairBinaryNoOneSplit
import AFTD.Kb.GameTheoryEconomics.IsEfxGoods

/-!
# efx_pair_binary_no_one_split_allocation

Topic: fair_division   Node: 691704cd9f65

Provenance: helper lemma. Structural helper for efx_four_agents_additive_exists (OP-7), campaign IN-404, 2026-11-01. Exact route obstruction from experiment 10993, not a counterexample to EFX existence; no novelty claim.

For the explicit binary nine-good matrix cast to real values, any allocation which preserves all but possibly one of the four old adjacent pairs fails EFX.
-/

open Function Finset

theorem efx_pair_binary_no_one_split_allocation (σ : Fin 9 → Fin 4) (r : Fin 4)
    (hstay : ∀ j : Fin 4, j ≠ r → σ (![0,2,4,6] j) = σ (![1,3,5,7] j)) :
    ¬ is_efx_goods (fun i g => (efx_pair_binary_values i g : ℝ)) σ := by
  fin_cases r
  · have h1 : σ 2 = σ 3 := hstay 1 (by decide)
    have h2 : σ 4 = σ 5 := hstay 2 (by decide)
    have h3 : σ 6 = σ 7 := hstay 3 (by decide)
    have heq : σ = efx_pair_binary_one_split 0 (σ 0) (σ 1) (σ 2) (σ 4) (σ 6) (σ 8) := by
      funext g
      fin_cases g <;> simp [efx_pair_binary_one_split, h1, h2, h3]
    rw [heq]
    exact efx_pair_binary_no_one_split 0 (σ 0) (σ 1) (σ 2) (σ 4) (σ 6) (σ 8)
  · have h0 : σ 0 = σ 1 := hstay 0 (by decide)
    have h2 : σ 4 = σ 5 := hstay 2 (by decide)
    have h3 : σ 6 = σ 7 := hstay 3 (by decide)
    have heq : σ = efx_pair_binary_one_split 1 (σ 0) (σ 2) (σ 3) (σ 4) (σ 6) (σ 8) := by
      funext g
      fin_cases g <;> simp [efx_pair_binary_one_split, h0, h2, h3]
    rw [heq]
    exact efx_pair_binary_no_one_split 1 (σ 0) (σ 2) (σ 3) (σ 4) (σ 6) (σ 8)
  · have h0 : σ 0 = σ 1 := hstay 0 (by decide)
    have h1 : σ 2 = σ 3 := hstay 1 (by decide)
    have h3 : σ 6 = σ 7 := hstay 3 (by decide)
    have heq : σ = efx_pair_binary_one_split 2 (σ 0) (σ 2) (σ 4) (σ 5) (σ 6) (σ 8) := by
      funext g
      fin_cases g <;> simp [efx_pair_binary_one_split, h0, h1, h3]
    rw [heq]
    exact efx_pair_binary_no_one_split 2 (σ 0) (σ 2) (σ 4) (σ 5) (σ 6) (σ 8)
  · have h0 : σ 0 = σ 1 := hstay 0 (by decide)
    have h1 : σ 2 = σ 3 := hstay 1 (by decide)
    have h2 : σ 4 = σ 5 := hstay 2 (by decide)
    have heq : σ = efx_pair_binary_one_split 3 (σ 0) (σ 2) (σ 4) (σ 6) (σ 7) (σ 8) := by
      funext g
      fin_cases g <;> simp [efx_pair_binary_one_split, h0, h1, h2]
    rw [heq]
    exact efx_pair_binary_no_one_split 3 (σ 0) (σ 2) (σ 4) (σ 6) (σ 7) (σ 8)
