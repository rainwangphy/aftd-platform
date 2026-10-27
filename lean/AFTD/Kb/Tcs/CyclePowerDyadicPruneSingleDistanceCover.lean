import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassMiddleParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_prune_single_distance_cover

Topic: combinatorics   Node: 0227b80a3804

Provenance: helper lemma. Routine localized pruning bridge for OP-205 / RT-1, arXiv:2610.15635 Section 3. Experiments6709 and6726 suggest a smaller pruning-stable signed dyadic-perturbation coverage family; they do not prove that family forces fullness. This helper only formalizes how any single shifted distance survives pruning.

Deleting and compressing the middle quarters preserves coverage at one fixed distance d below the new radius, using only original coverage at half the old radius plus d. Tight dyadic class weight is assumed. There is no coverage assumption at any other distance and no claim of active-count preservation.
-/

open Finset

theorem cycle_power_dyadic_prune_single_distance_cover
    (k d : ℕ) (x : ℤ → ℕ → Bool) (hd : 1 ≤ d) (hdH : d < 2^(k+1))
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+2) (x p) =
      (range (2^(k+2))).sum (fun a => (x p a).toNat))
    (hcover : ∀ v : ℤ, ∃ a : ℕ, a < 2^(k+2)-(2^(k+1)+d) ∧
      x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+(2^(k+1)+d)) = true) :
    ∀ v : ℤ, ∃ a : ℕ, a < 2^(k+1)-d ∧
      cycle_power_dyadic_b_lift k (x (v-(a : ℤ))) a = true ∧
      cycle_power_dyadic_b_lift k (x (v-(a : ℤ))) (a+d) = true := by
  intro v
  have hleft : ∀ (p : ℤ) (a : ℕ), 2 ^ k ≤ a → a < 2 ^ (k + 1) →
      x p a = true → x p (a + 2 ^ (k + 1)) = true :=
    fun p => (cycle_power_dyadic_tight_class_middle_parent k (x p) (htight p)).1
  have hright : ∀ (p : ℤ) (a : ℕ), 2 ^ (k + 1) ≤ a → a < 3 * 2 ^ k →
      x p a = true → x p (a - 2 ^ (k + 1)) = true :=
    fun p => (cycle_power_dyadic_tight_class_middle_parent k (x p) (htight p)).2
  obtain ⟨a, ha, h0, h1⟩ := hcover v
  have hH : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
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
