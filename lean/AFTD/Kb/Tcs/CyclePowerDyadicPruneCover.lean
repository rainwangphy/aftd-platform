import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassMiddleParent
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCoverOfMiddleParent

/-!
# cycle_power_dyadic_prune_cover

Topic: combinatorics   Node: d3ec7c46c7dd

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

Deleting each tight dyadic class's middle two quarters and compressing its outer quarters preserves coverage of all distances smaller than the new radius, keeping the original class start indices.
-/

open Finset

theorem cycle_power_dyadic_prune_cover
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k + 2) (x p) =
      (range (2 ^ (k + 2))).sum (fun i => (x p i).toNat))
    (hcover : ∀ (d : ℕ), 1 ≤ d → d < 2 ^ (k + 2) → ∀ v : ℤ,
      ∃ a < 2 ^ (k + 2) - d, x (v - (a : ℤ)) a = true ∧
        x (v - (a : ℤ)) (a + d) = true) :
    ∀ (d : ℕ), 1 ≤ d → d < 2 ^ (k + 1) → ∀ v : ℤ,
      ∃ a < 2 ^ (k + 1) - d,
        cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) a = true ∧
        cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) (a + d) = true := by
  have hp := fun p => cycle_power_dyadic_tight_class_middle_parent k (x p) (htight p)
  exact cycle_power_dyadic_prune_cover_of_middle_parent k x (fun p => (hp p).1) (fun p => (hp p).2) hcover
