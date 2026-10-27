import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjection
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_outer_projection_prune

Topic: combinatorics   Node: 572137f2747e

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The all-scale shell fullness conditions are explicit hypotheses when used; they have not been derived from optimal active counts. No graph covering value or research advance is claimed.

Successive direct outer projections form a compatible middle-quarter pruning hierarchy.
-/

open Finset

theorem cycle_power_dyadic_outer_projection_prune
    (m r : ℕ) (hr : r+2 ≤ m) (b : ℕ → Bool) :
    cycle_power_dyadic_b_lift r (cycle_power_dyadic_outer_projection m (r+1) b) =
      cycle_power_dyadic_outer_projection m r b := by
  have hp : 2^(r+2) ≤ 2^m := Nat.pow_le_pow_right (by decide) hr
  have hH : 2^(r+1)=2*2^r := by rw [pow_succ]; omega
  have hD : 2^(r+2)=2*2^(r+1) := by rw [pow_succ]; omega
  funext a
  by_cases ha : a < 2^r
  · have hi : a < 2^(r+1) := by omega
    simp only [cycle_power_dyadic_b_lift,if_pos ha,
      cycle_power_dyadic_outer_projection,if_pos hi,if_pos ha]
  · have hi : ¬a+2^(r+1) < 2^(r+1) := by omega
    simp only [cycle_power_dyadic_b_lift,if_neg ha,
      cycle_power_dyadic_outer_projection,if_neg hi,if_neg ha]
    congr 1
    omega
