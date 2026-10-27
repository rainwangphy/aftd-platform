import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_b_lift_high

Topic: combinatorics   Node: 18f82d91ee90

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

Middle-quarter pruning maps every smaller-scale right endpoint to its original larger-scale position.
-/

open Finset

theorem cycle_power_dyadic_b_lift_high (k j a : ℕ) (hjk : j ≤ k) (ha : a < 2 ^ j) (b : ℕ → Bool) :
    cycle_power_dyadic_b_lift k b (a + 2 ^ (k + 1) - 2 ^ j) =
      b (a + 2 ^ (k + 2) - 2 ^ j) := by
  have hpow : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hjk
  have hH : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  have hD : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
  dsimp [cycle_power_dyadic_b_lift]
  rw [if_neg (by omega : ¬a + 2 ^ (k + 1) - 2 ^ j < 2 ^ k)]
  congr 1
  omega
