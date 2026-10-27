import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjection
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_outer_projection_comp_prune

Topic: combinatorics   Node: ada769703fe5

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The all-scale shell fullness conditions are explicit hypotheses when used; they have not been derived from optimal active counts. No graph covering value or research advance is claimed.

A direct projection after deleting the original middle quarters equals the same direct projection of the original class at every smaller valid radius.
-/

open Finset

theorem cycle_power_dyadic_outer_projection_comp_prune
    (M r : ℕ) (hr : r ≤ M) (b : ℕ → Bool) :
    cycle_power_dyadic_outer_projection (M+1) r (cycle_power_dyadic_b_lift M b) =
      cycle_power_dyadic_outer_projection (M+2) r b := by
  have hp : 2^r ≤ 2^M := Nat.pow_le_pow_right (by decide) hr
  have hR : 2^(r+1)=2*2^r := by rw [pow_succ]; omega
  have hH : 2^(M+1)=2*2^M := by rw [pow_succ]; omega
  have hD : 2^(M+2)=2*2^(M+1) := by rw [pow_succ]; omega
  funext a
  by_cases ha : a < 2^r
  · have haM : a < 2^M := by omega
    simp only [cycle_power_dyadic_outer_projection,if_pos ha,
      cycle_power_dyadic_b_lift,if_pos haM]
  · have hi : ¬a+2^(M+1)-2^(r+1) < 2^M := by omega
    simp only [cycle_power_dyadic_outer_projection,if_neg ha,
      cycle_power_dyadic_b_lift,if_neg hi]
    congr 1
    omega
