import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_prune_cover_of_middle_parent

Topic: combinatorics   Node: b0026b1fbf3e

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

If every selected middle-quarter position has its matched outer-quarter parent selected, deleting and compressing the middle quarters preserves coverage of every smaller distance. The class start indices are unchanged.
-/

open Finset

theorem cycle_power_dyadic_prune_cover_of_middle_parent
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (hleft : ∀ (p : ℤ) (a : ℕ), 2 ^ k ≤ a → a < 2 ^ (k + 1) →
      x p a = true → x p (a + 2 ^ (k + 1)) = true)
    (hright : ∀ (p : ℤ) (a : ℕ), 2 ^ (k + 1) ≤ a → a < 3 * 2 ^ k →
      x p a = true → x p (a - 2 ^ (k + 1)) = true)
    (hcover : ∀ (d : ℕ), 1 ≤ d → d < 2 ^ (k + 2) → ∀ v : ℤ,
      ∃ a < 2 ^ (k + 2) - d, x (v - (a : ℤ)) a = true ∧
        x (v - (a : ℤ)) (a + d) = true) :
    ∀ (d : ℕ), 1 ≤ d → d < 2 ^ (k + 1) → ∀ v : ℤ,
      ∃ a < 2 ^ (k + 1) - d,
        cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) a = true ∧
        cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) (a + d) = true := by
  intro d hd hdh v
  have hp1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  have hp2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
  obtain ⟨a, ha, h0, h1⟩ := hcover (2 ^ (k + 1) + d) (by omega) (by omega) v
  refine ⟨a, by omega, ?_, ?_⟩
  · dsimp [cycle_power_dyadic_b_lift]
    split_ifs with hal
    · exact h0
    · exact hleft _ a (by omega) (by omega) h0
  · dsimp [cycle_power_dyadic_b_lift]
    split_ifs with hal
    · have hb := hright (v - (a : ℤ)) (a + (2 ^ (k + 1) + d)) (by omega) (by omega) h1
      have he : a + (2 ^ (k + 1) + d) - 2 ^ (k + 1) = a + d := by omega
      simpa only [he] using hb
    · have he : a + d + 2 ^ (k + 1) = a + (2 ^ (k + 1) + d) := by omega
      simpa only [he] using h1
