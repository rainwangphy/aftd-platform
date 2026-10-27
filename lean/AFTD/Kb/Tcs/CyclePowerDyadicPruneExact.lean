import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_prune_exact

Topic: combinatorics   Node: bb5be2b411de

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

Deleting the middle two quarters of every class preserves every smaller-scale exact dyadic long-edge count, without changing the class start indices.
-/

open Finset

theorem cycle_power_dyadic_prune_exact
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < k + 2, ∀ v : ℤ,
      (range (2 ^ j)).sum (fun a =>
        (x (v - (a : ℤ)) a &&
          x (v - (a : ℤ)) (a + 2 ^ (k + 2) - 2 ^ j)).toNat) = 1) :
    ∀ j < k + 1, ∀ v : ℤ,
      (range (2 ^ j)).sum (fun a =>
        (cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) a &&
          cycle_power_dyadic_b_lift k (x (v - (a : ℤ)))
            (a + 2 ^ (k + 1) - 2 ^ j)).toNat) = 1 := by
  intro j hj v
  refine Eq.trans ?_ (hexact j (by omega) v)
  apply sum_congr rfl
  intro a ha
  have haj : a < 2 ^ j := mem_range.mp ha
  have hjk : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) (by omega)
  have hp1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  have hp2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
  have hl : a < 2 ^ k := by omega
  have hr : ¬a + 2 ^ (k + 1) - 2 ^ j < 2 ^ k := by omega
  dsimp [cycle_power_dyadic_b_lift]
  rw [if_pos hl, if_neg hr]
  have he : a + 2 ^ (k + 1) - 2 ^ j + 2 ^ (k + 1) = a + 2 ^ (k + 2) - 2 ^ j := by omega
  rw [he]
