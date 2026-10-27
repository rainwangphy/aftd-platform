import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicPairCount
import AFTD.Kb.Tcs.CyclePowerDyadicBLiftLow
import AFTD.Kb.Tcs.CyclePowerDyadicBLiftHigh
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_pair_count_prune

Topic: combinatorics   Node: 5f05fb85774d

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

Deleting the middle two quarters preserves each smaller dyadic pair count.
-/

open Finset

theorem cycle_power_dyadic_pair_count_prune (k j : ℕ) (hj : j ≤ k) (b : ℕ → Bool) :
    cycle_power_dyadic_pair_count (k + 2) j b =
      cycle_power_dyadic_pair_count (k + 1) j (cycle_power_dyadic_b_lift k b) := by
  apply sum_congr rfl
  intro a ha
  rw [cycle_power_dyadic_b_lift_low k j a hj (mem_range.mp ha),
    cycle_power_dyadic_b_lift_high k j a hj (mem_range.mp ha)]
