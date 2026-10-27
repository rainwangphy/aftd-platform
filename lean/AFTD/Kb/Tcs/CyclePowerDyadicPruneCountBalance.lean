import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerMiddleQuarterPruneCountBalance
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassMiddleParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_prune_count_balance

Topic: combinatorics   Node: f722a2cebb0b

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

Tight dyadic classes with constant active count t+1 and exact half-distance coverage satisfy the exact pruning balance C_pruned(v)+R(v)=t+R(v+H).
-/

open Finset

theorem cycle_power_dyadic_prune_count_balance
    (k t : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k + 2) (x p) =
      (range (2 ^ (k + 2))).sum (fun a => (x p a).toNat))
    (hcount : ∀ v, (range (2 ^ (k + 2))).sum
      (fun a => (x (v - (a : ℤ)) a).toNat) = t + 1)
    (hhalf : ∀ v, (range (2 ^ (k + 1))).sum
      (fun a => (x (v - (a : ℤ)) a &&
        x (v - (a : ℤ)) (a + 2 ^ (k + 1))).toNat) = 1) :
    ∀ v : ℤ,
      (range (2 ^ (k + 1))).sum (fun a =>
        (cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) a).toNat) +
      (range (2 ^ (k + 1))).sum (fun a =>
        (x (v - ((2 ^ (k + 1) + a : ℕ) : ℤ)) (2 ^ (k + 1) + a)).toNat) =
      t + (range (2 ^ (k + 1))).sum (fun a =>
        (x ((v + (2 ^ (k + 1) : ℕ)) - ((2 ^ (k + 1) + a : ℕ) : ℤ))
          (2 ^ (k + 1) + a)).toNat) := by
  have hH : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
  have hD : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; norm_num; omega
  have hp := fun p => cycle_power_dyadic_tight_class_middle_parent k (x p) (htight p)
  have hleft : ∀ (p : ℤ) (a : ℕ), 2 ^ k ≤ a → a < 2 * 2 ^ k →
      x p a = true → x p (a + 2 * 2 ^ k) = true := by
    intro p a ha hb hx
    have hh := (hp p).1 a ha (by simpa only [hH] using hb) hx
    simpa only [hH] using hh
  have hright : ∀ (p : ℤ) (a : ℕ), 2 * 2 ^ k ≤ a → a < 3 * 2 ^ k →
      x p a = true → x p (a - 2 * 2 ^ k) = true := by
    intro p a ha hb hx
    have hh := (hp p).2 a (by simpa only [hH] using ha) hb hx
    simpa only [hH] using hh
  have hc : ∀ v, (range (4 * 2 ^ k)).sum
      (fun a => (x (v - (a : ℤ)) a).toNat) = t + 1 := by
    simpa only [hD] using hcount
  have he : ∀ v, (range (2 * 2 ^ k)).sum
      (fun a => (x (v - (a : ℤ)) a &&
        x (v - (a : ℤ)) (a + 2 * 2 ^ k)).toNat) = 1 := by
    simpa only [hH] using hhalf
  have hb := cycle_power_middle_quarter_prune_count_balance (2 ^ k) t x hleft hright hc he
  intro v
  have hshift : (range (2 ^ (k + 1))).sum (fun a =>
        (x ((v + (2 ^ (k + 1) : ℕ)) - ((2 ^ (k + 1) + a : ℕ) : ℤ))
          (2 ^ (k + 1) + a)).toNat) =
      (range (2 ^ (k + 1))).sum (fun a =>
        (x (v - (a : ℤ)) (2 ^ (k + 1) + a)).toNat) := by
    apply sum_congr rfl
    intro a ha
    have heq : (v + (2 ^ (k + 1) : ℕ)) - ((2 ^ (k + 1) + a : ℕ) : ℤ) = v - (a : ℤ) := by
      push_cast
      ring
    rw [heq]
  rw [hshift]
  simpa only [cycle_power_dyadic_b_lift, hH] using hb v
