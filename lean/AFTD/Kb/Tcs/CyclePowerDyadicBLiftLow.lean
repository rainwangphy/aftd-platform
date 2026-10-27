import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_b_lift_low

Topic: combinatorics   Node: 75cf7578e756

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

Middle-quarter pruning preserves every smaller-scale left position.
-/

open Finset

theorem cycle_power_dyadic_b_lift_low (k j a : ℕ) (hjk : j ≤ k) (ha : a < 2 ^ j) (b : ℕ → Bool) :
    cycle_power_dyadic_b_lift k b a = b a := by
  have hpow : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hjk
  dsimp [cycle_power_dyadic_b_lift]
  rw [if_pos (by omega : a < 2 ^ k)]
