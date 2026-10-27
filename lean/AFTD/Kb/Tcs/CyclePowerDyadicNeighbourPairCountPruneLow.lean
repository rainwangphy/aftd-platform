import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicNeighbourPairCount
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_neighbour_pair_count_prune_low

Topic: combinatorics   Node: 462055fe37da

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

Deleting the middle two quarters preserves each strictly smaller neighbour pair count.
-/

open Finset

theorem cycle_power_dyadic_neighbour_pair_count_prune_low
    (k j : ℕ) (hj : j < k) (b : ℕ → Bool) :
    cycle_power_dyadic_neighbour_pair_count (k + 2) j b =
      cycle_power_dyadic_neighbour_pair_count (k + 1) j (cycle_power_dyadic_b_lift k b) := by
  have hpow : 2 ^ j < 2 ^ k := Nat.pow_lt_pow_right (by decide) hj
  have hH : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  have hD : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
  apply sum_congr rfl
  intro a ha
  have ha : a ≤ 2 ^ j := by simpa only [mem_range, Nat.lt_succ_iff] using ha
  have hlo : cycle_power_dyadic_b_lift k b a = b a := by
    dsimp [cycle_power_dyadic_b_lift]; rw [if_pos (by omega)]
  have hhi : cycle_power_dyadic_b_lift k b (a + 2 ^ (k + 1) - 2 ^ j - 1) =
      b (a + 2 ^ (k + 2) - 2 ^ j - 1) := by
    dsimp [cycle_power_dyadic_b_lift]
    rw [if_neg (by omega)]
    congr 1; omega
  rw [hlo, hhi]
