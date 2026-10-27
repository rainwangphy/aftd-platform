import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_tight_class_prune

Topic: combinatorics   Node: 01bd3c9f5aea

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

Deleting a tight dyadic class's middle two quarters and compressing the remaining outer quarters preserves equality between its dyadic weight and its cardinality.
-/

open Finset

theorem cycle_power_dyadic_tight_class_prune (k : ℕ) (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight (k + 2) b =
      (range (2 ^ (k + 2))).sum (fun i => (b i).toNat)) :
    cycle_power_dyadic_class_weight (k + 1) (cycle_power_dyadic_b_lift k b) =
      (range (2 ^ (k + 1))).sum (fun i => (cycle_power_dyadic_b_lift k b i).toNat) := by
  have hsplit := cycle_power_dyadic_class_weight_succ k b
  have hsmall := cycle_power_dyadic_class_weight_le_aux k (cycle_power_dyadic_b_lift k b)
  have htotal := cycle_power_dyadic_sum_lift_and_cross_le k b
  omega
