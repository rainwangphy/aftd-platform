import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDefectiveHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicAlternatingHalfTight
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.CyclePowerDyadicBoundaryPairOfAlternating
import AFTD.Kb.Tcs.CyclePowerSumRangeDouble
import AFTD.Kb.Tcs.CyclePowerDyadicAlternatingHalfModel

/-!
# cycle_power_dyadic_alternating_defective_halves

Topic: combinatorics   Node: 661b6e3a981e

Provenance: helper lemma. Two-phase parity-reindexing bridge for the defective half-model route in RT-1.

Parity reindexing of an alternating model with only its two possible middle defects yields the two defective half models, with phases zero and half the half-span.
-/

theorem cycle_power_dyadic_defective_halves_parity (x : ℤ → ℕ → Bool)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1) (s : ℤ) (hs : x s 1 = false) :
    (∀ q : ℤ, x (s + 2*q + 1) 1 = true) ∧ (∀ k : ℤ, x (s + 2*k) 1 = false) := by
  have hs1 : x (s+1) 1 = true := by rw [halt, hs]; rfl
  have hpar := cycle_power_dyadic_alternating_bit_one_parity x halt (s+1) hs1
  refine ⟨fun q => ?_, fun k => ?_⟩
  · have := (hpar q).1; rwa [show 2*q+(s+1) = s+2*q+1 by ring] at this
  · have := (hpar (k-1)).2; rwa [show 2*(k-1)+(s+1)+1 = s+2*k by ring] at this

theorem cycle_power_dyadic_defective_halves_lower (t : ℕ) (ht : 2 ≤ t) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t → x p j = false)
    (s : ℤ) (hs : x s 1 = false) (e : ℕ) (he : e < 2) :
    ∀ j, j + 1 < t → ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (s + 2*(v-(a:ℤ)) + 1) (2*a+e) && x (s + 2*(v-(a:ℤ)) + 1) (2*(a+2^t-2^j)+e)).toNat) = 1 := by
  intro j hj v
  obtain ⟨htrue, hfalse⟩ := cycle_power_dyadic_defective_halves_parity x halt s hs
  have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; omega
  have hpj : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; omega
  have hjt : 2 ^ (j + 1) ≤ 2 ^ (t-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have ht1 : 2 ^ t = 2 * 2 ^ (t-1) := by
    rw [← pow_succ']; congr 1; omega
  have hj1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have h := hexact (j + 1) (by omega) (s + 2 * v + 1 + e)
  rw [hpj, cycle_power_sum_range_double, Finset.sum_add_distrib] at h
  interval_cases e
  · have hz : (Finset.range (2 ^ j)).sum (fun i =>
        (x (s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1) &&
          x (s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1 + 2 ^ (t + 1) - 2 * 2 ^ j)).toNat) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hr : s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ) = s + 2 * (v - i) := by
        push_cast; ring
      rw [hr, hpart _ (hfalse _) (2 * i + 1) (by omega) (by omega) (by omega) (by omega)]
      rfl
    rw [hz, Nat.add_zero] at h
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hr : s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * i : ℕ) : ℤ) = s + 2 * (v - i) + 1 := by
      push_cast; ring
    have ho : 2 * i + 2 ^ (t + 1) - 2 * 2 ^ j = 2 * (i + 2 ^ t - 2 ^ j) + 0 := by omega
    rw [hr, ho]
    simp only [Nat.add_zero]
  · have hz : (Finset.range (2 ^ j)).sum (fun i =>
        (x (s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ)) (2 * i) &&
          x (s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ)) (2 * i + 2 ^ (t + 1) - 2 * 2 ^ j)).toNat) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hr : s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ) = s + 2 * (v - i + 1) := by
        push_cast; ring
      rw [hr, hpart _ (hfalse _) (2 * i + 2 ^ (t + 1) - 2 * 2 ^ j) (by omega) (by omega) (by omega) (by omega)]
      simp
    rw [hz, Nat.zero_add] at h
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hr : s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ) = s + 2 * (v - i) + 1 := by
      push_cast; ring
    have ho : 2 * i + 1 + 2 ^ (t + 1) - 2 * 2 ^ j = 2 * (i + 2 ^ t - 2 ^ j) + 1 := by omega
    rw [hr, ho]

theorem cycle_power_dyadic_defective_halves_cover (t : ℕ) (ht : 2 ≤ t) (x : ℤ → ℕ → Bool)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t → x p j = false)
    (s : ℤ) (hs : x s 1 = false) (e : ℕ) (he : e < 2) :
    ∀ d : ℕ, 1 ≤ d → d < 2^t → d ≠ 2^(t-1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^t-d ∧ x (s + 2*(v-(a:ℤ)) + 1) (2*a+e) = true ∧
        x (s + 2*(v-(a:ℤ)) + 1) (2*(a+d)+e) = true := by
  intro d hd hdt hdh v
  obtain ⟨htrue, hfalse⟩ := cycle_power_dyadic_defective_halves_parity x halt s hs
  have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; omega
  have ht1 : 2 ^ t = 2 * 2 ^ (t-1) := by
    rw [← pow_succ']; congr 1; omega
  obtain ⟨a, ha, h1, h2⟩ := hcover (2 * d) (by omega) (by omega) (s + 2 * v + 1 + e)
  rcases Nat.even_or_odd' a with ⟨a', rfl | rfl⟩ <;> interval_cases e
  · refine ⟨a', by omega, ?_, ?_⟩
    · have hr : s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * a' : ℕ) : ℤ) = s + 2 * (v - a') + 1 := by
        push_cast; ring
      rw [hr] at h1; simpa using h1
    · have hr : s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * a' : ℕ) : ℤ) = s + 2 * (v - a') + 1 := by
        push_cast; ring
      rw [hr, show 2 * a' + 2 * d = 2 * (a' + d) by ring] at h2; simpa using h2
  · exfalso
    have hr : s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * a' : ℕ) : ℤ) = s + 2 * (v - a' + 1) := by
      push_cast; ring
    rw [hr] at h1 h2
    by_cases hc : 2 * a' + 2 * d = 2 ^ t
    · rw [hpart _ (hfalse _) (2 * a') (by omega) (by omega) (by omega) (by omega)] at h1
      exact Bool.false_ne_true h1
    · rw [hpart _ (hfalse _) (2 * a' + 2 * d) (by omega) (by omega) (by omega) hc] at h2
      exact Bool.false_ne_true h2
  · exfalso
    have hr : s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * a' + 1 : ℕ) : ℤ) = s + 2 * (v - a') := by
      push_cast; ring
    rw [hr] at h1 h2
    have hb : 2 * a' + 1 = 2 ^ t - 1 := by
      by_contra hne
      rw [hpart _ (hfalse _) (2 * a' + 1) (by omega) (by omega) hne (by omega)] at h1
      exact Bool.false_ne_true h1
    rw [hpart _ (hfalse _) (2 * a' + 1 + 2 * d) (by omega) (by omega) (by omega) (by omega)] at h2
    exact Bool.false_ne_true h2
  · refine ⟨a', by omega, ?_, ?_⟩
    · have hr : s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * a' + 1 : ℕ) : ℤ) = s + 2 * (v - a') + 1 := by
        push_cast; ring
      rw [hr] at h1; exact h1
    · have hr : s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * a' + 1 : ℕ) : ℤ) = s + 2 * (v - a') + 1 := by
        push_cast; ring
      rw [hr, show 2 * a' + 1 + 2 * d = 2 * (a' + d) + 1 by ring] at h2; exact h2

theorem cycle_power_dyadic_defective_halves_top_even (t : ℕ) (ht : 2 ≤ t) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t → x p j = false)
    (s : ℤ) (hs : x s 1 = false) :
    ∀ v : ℤ, (Finset.range (2^(t-1))).sum (fun a =>
      (x (s + 2*(v-(a:ℤ)) + 1) (2*a) && x (s + 2*(v-(a:ℤ)) + 1) (2*(a+2^t-2^(t-1)))).toNat) +
      (x (s + 2*(v+0) + 2 - ((2^t : ℕ) : ℤ)) (2^t - 1)).toNat = 1 := by
  intro v
  obtain ⟨htrue, hfalse⟩ := cycle_power_dyadic_defective_halves_parity x halt s hs
  have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; omega
  have ht1 : 2 ^ t = 2 * 2 ^ (t-1) := by
    rw [← pow_succ']; congr 1; omega
  have ht2 : 2 ≤ 2 ^ (t-1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (t-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hendp := cycle_power_dyadic_exact_endpoints (t+1) (by omega) x hexact
  have h := hexact t (by omega) (s + 2 * v + 1)
  rw [ht1, cycle_power_sum_range_double, Finset.sum_add_distrib] at h
  have hodd : (Finset.range (2 ^ (t-1))).sum (fun i =>
      (x (s + 2 * v + 1 - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1) &&
        x (s + 2 * v + 1 - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1 + 2 ^ (t + 1) - 2 * 2 ^ (t-1))).toNat) =
      (x (s + 2*(v+0) + 2 - ((2^t : ℕ) : ℤ)) (2^t - 1)).toNat := by
    rw [Finset.sum_eq_single (2 ^ (t-1) - 1)]
    · have hr : s + 2 * v + 1 - ((2 * (2 ^ (t-1) - 1) + 1 : ℕ) : ℤ) =
          s + 2*(v+0) + 2 - ((2^t : ℕ) : ℤ) := by omega
      have hb1 : 2 * (2 ^ (t-1) - 1) + 1 = 2 ^ t - 1 := by omega
      have hb2 : 2 * (2 ^ (t-1) - 1) + 1 + 2 ^ (t + 1) - 2 * 2 ^ (t-1) = 2 ^ (t+1) - 1 := by omega
      rw [hr, hb2, hb1, (hendp _).2, Bool.and_true]
    · intro i hi hne
      have hi' := Finset.mem_range.mp hi
      have hr : s + 2 * v + 1 - ((2 * i + 1 : ℕ) : ℤ) = s + 2 * (v - i) := by push_cast; ring
      rw [hr, hpart _ (hfalse _) (2 * i + 1) (by omega) (by omega) (by omega) (by omega)]
      rfl
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have heven : (Finset.range (2^(t-1))).sum (fun a =>
      (x (s + 2*(v-(a:ℤ)) + 1) (2*a) && x (s + 2*(v-(a:ℤ)) + 1) (2*(a+2^t-2^(t-1)))).toNat) =
      (Finset.range (2 ^ (t-1))).sum (fun i =>
      (x (s + 2 * v + 1 - ((2 * i : ℕ) : ℤ)) (2 * i) &&
        x (s + 2 * v + 1 - ((2 * i : ℕ) : ℤ)) (2 * i + 2 ^ (t + 1) - 2 * 2 ^ (t-1))).toNat) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hr : s + 2 * v + 1 - ((2 * i : ℕ) : ℤ) = s + 2 * (v - i) + 1 := by push_cast; ring
    have ho : 2 * i + 2 ^ (t + 1) - 2 * 2 ^ (t-1) = 2 * (i + 2 ^ t - 2 ^ (t-1)) := by omega
    rw [hr, ho]
  rw [heven, ← hodd]; exact h

theorem cycle_power_dyadic_defective_halves_top_odd (t : ℕ) (ht : 2 ≤ t) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t → x p j = false)
    (s : ℤ) (hs : x s 1 = false) :
    ∀ v : ℤ, (Finset.range (2^(t-1))).sum (fun a =>
      (x (s + 2*(v-(a:ℤ)) + 1) (2*a+1) && x (s + 2*(v-(a:ℤ)) + 1) (2*(a+2^t-2^(t-1))+1)).toNat) +
      (x (s + 2*(v+(2:ℤ)^(t-1)) + 2 - ((2^t : ℕ) : ℤ)) (2^t)).toNat = 1 := by
  intro v
  obtain ⟨htrue, hfalse⟩ := cycle_power_dyadic_defective_halves_parity x halt s hs
  have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; omega
  have ht1 : 2 ^ t = 2 * 2 ^ (t-1) := by
    rw [← pow_succ']; congr 1; omega
  have ht2 : 2 ≤ 2 ^ (t-1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (t-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hz2 : ((2^t : ℕ) : ℤ) = 2 * (2:ℤ)^(t-1) := by rw [ht1]; push_cast; ring
  have hendp := cycle_power_dyadic_exact_endpoints (t+1) (by omega) x hexact
  have h := hexact t (by omega) (s + 2 * v + 2)
  rw [ht1, cycle_power_sum_range_double, Finset.sum_add_distrib] at h
  have hev : (Finset.range (2 ^ (t-1))).sum (fun i =>
      (x (s + 2 * v + 2 - ((2 * i : ℕ) : ℤ)) (2 * i) &&
        x (s + 2 * v + 2 - ((2 * i : ℕ) : ℤ)) (2 * i + 2 ^ (t + 1) - 2 * 2 ^ (t-1))).toNat) =
      (x (s + 2*(v+(2:ℤ)^(t-1)) + 2 - ((2^t : ℕ) : ℤ)) (2^t)).toNat := by
    rw [Finset.sum_eq_single 0]
    · have hr : s + 2 * v + 2 - ((2 * 0 : ℕ) : ℤ) = s + 2*(v+(2:ℤ)^(t-1)) + 2 - ((2^t : ℕ) : ℤ) := by
        rw [hz2]; push_cast; ring
      have hb2 : 2 * 0 + 2 ^ (t + 1) - 2 * 2 ^ (t-1) = 2 ^ t := by omega
      rw [hr, hb2, Nat.mul_zero, (hendp _).1, Bool.true_and]
    · intro i hi hne
      have hi' := Finset.mem_range.mp hi
      have hr : s + 2 * v + 2 - ((2 * i : ℕ) : ℤ) = s + 2 * (v - i + 1) := by push_cast; ring
      rw [hr, hpart _ (hfalse _) (2 * i) (by omega) (by omega) (by omega) (by omega)]
      rfl
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hodd : (Finset.range (2^(t-1))).sum (fun a =>
      (x (s + 2*(v-(a:ℤ)) + 1) (2*a+1) && x (s + 2*(v-(a:ℤ)) + 1) (2*(a+2^t-2^(t-1))+1)).toNat) =
      (Finset.range (2 ^ (t-1))).sum (fun i =>
      (x (s + 2 * v + 2 - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1) &&
        x (s + 2 * v + 2 - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1 + 2 ^ (t + 1) - 2 * 2 ^ (t-1))).toNat) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hr : s + 2 * v + 2 - ((2 * i + 1 : ℕ) : ℤ) = s + 2 * (v - i) + 1 := by push_cast; ring
    have ho : 2 * i + 1 + 2 ^ (t + 1) - 2 * 2 ^ (t-1) = 2 * (i + 2 ^ t - 2 ^ (t-1)) + 1 := by omega
    rw [hr, ho]
  rw [hodd, ← hev]; omega

theorem cycle_power_dyadic_defective_halves_count (t : ℕ) (ht : 2 ≤ t) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1)
    (hcount : ∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (t+1)+1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t → x p j = false)
    (s : ℤ) (hs : x s 1 = false) (e : ℕ) (he : e < 2) :
    ∀ v : ℤ, (Finset.range (2^t)).sum (fun a => (x (s + 2*(v-(a:ℤ)) + 1) (2*a+e)).toNat) +
      (x (s + 2*v + 2 - ((2^t : ℕ) : ℤ)) (2^t - 1 + e)).toNat = t+1 := by
  intro v
  obtain ⟨htrue, hfalse⟩ := cycle_power_dyadic_defective_halves_parity x halt s hs
  have hpow : 2 ^ (t + 1) = 2 * 2 ^ t := by rw [pow_succ]; omega
  have ht1 : 2 ^ t = 2 * 2 ^ (t-1) := by
    rw [← pow_succ']; congr 1; omega
  have ht2 : 2 ≤ 2 ^ (t-1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (t-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hendp := cycle_power_dyadic_exact_endpoints (t+1) (by omega) x hexact
  have h := hcount (s + 2 * v + 1 + e)
  rw [hpow, cycle_power_sum_range_double, Finset.sum_add_distrib] at h
  interval_cases e
  · have hodd : (Finset.range (2 ^ t)).sum (fun i =>
        (x (s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1)).toNat) =
        (x (s + 2*v + 2 - ((2^t : ℕ) : ℤ)) (2^t - 1 + 0)).toNat + 1 := by
      rw [Finset.sum_eq_add (2 ^ (t-1) - 1) (2 ^ t - 1) (by omega)]
      · have hr : s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * (2 ^ (t-1) - 1) + 1 : ℕ) : ℤ) =
            s + 2*v + 2 - ((2^t : ℕ) : ℤ) := by omega
        have hb1 : 2 * (2 ^ (t-1) - 1) + 1 = 2 ^ t - 1 + 0 := by omega
        have hb2 : 2 * (2 ^ t - 1) + 1 = 2 ^ (t+1) - 1 := by omega
        rw [hr, hb1, hb2, (hendp _).2]; rfl
      · intro i hi hne
        have hi' := Finset.mem_range.mp hi
        have hr : s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ) = s + 2 * (v - i) := by
          push_cast; ring
        rw [hr, hpart _ (hfalse _) (2 * i + 1) (by omega) (by omega) (by omega) (by omega)]
        rfl
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    have heven : (Finset.range (2^t)).sum (fun a => (x (s + 2*(v-(a:ℤ)) + 1) (2*a+0)).toNat) =
        (Finset.range (2 ^ t)).sum (fun i =>
        (x (s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * i : ℕ) : ℤ)) (2 * i)).toNat) := by
      apply Finset.sum_congr rfl
      intro i _
      have hr : s + 2 * v + 1 + ((0:ℕ):ℤ) - ((2 * i : ℕ) : ℤ) = s + 2 * (v - i) + 1 := by
        push_cast; ring
      rw [hr, Nat.add_zero]
    rw [heven]; omega
  · have hev : (Finset.range (2 ^ t)).sum (fun i =>
        (x (s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ)) (2 * i)).toNat) =
        1 + (x (s + 2*v + 2 - ((2^t : ℕ) : ℤ)) (2^t - 1 + 1)).toNat := by
      rw [Finset.sum_eq_add 0 (2 ^ (t-1)) (by omega)]
      · have hr : s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * 2 ^ (t-1) : ℕ) : ℤ) =
            s + 2*v + 2 - ((2^t : ℕ) : ℤ) := by rw [← ht1]; push_cast; ring
        have hb1 : 2 * 2 ^ (t-1) = 2 ^ t - 1 + 1 := by omega
        rw [hr, hb1, Nat.mul_zero, (hendp _).1]; rfl
      · intro i hi hne
        have hi' := Finset.mem_range.mp hi
        have hr : s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ) = s + 2 * (v - i + 1) := by
          push_cast; ring
        rw [hr, hpart _ (hfalse _) (2 * i) (by omega) (by omega) (by omega) (by omega)]
        rfl
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    have hodd : (Finset.range (2^t)).sum (fun a => (x (s + 2*(v-(a:ℤ)) + 1) (2*a+1)).toNat) =
        (Finset.range (2 ^ t)).sum (fun i =>
        (x (s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1)).toNat) := by
      apply Finset.sum_congr rfl
      intro i _
      have hr : s + 2 * v + 1 + ((1:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ) = s + 2 * (v - i) + 1 := by
        push_cast; ring
      rw [hr]
    rw [hodd]; omega

theorem cycle_power_dyadic_alternating_defective_halves (t : ℕ) (ht : 2 ≤ t) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
      (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < t+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (t+1)+1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(t+1) - 1 → j ≠ 2^t - 1 → j ≠ 2^t → x p j = false) (s : ℤ) (hs : x s 1 = false) :
    cycle_power_dyadic_defective_half_model t (fun q a => x (s + 2*q + 1) (2*a))
      (fun v => x (s + 2*v + 2 - ((2^t : ℕ) : ℤ)) (2^t - 1)) 0 ∧
    cycle_power_dyadic_defective_half_model t (fun q a => x (s + 2*q + 1) (2*a+1))
      (fun v => x (s + 2*v + 2 - ((2^t : ℕ) : ℤ)) (2^t)) ((2 : ℤ)^(t-1)) := by
  obtain ⟨htrue, hfalse⟩ := cycle_power_dyadic_defective_halves_parity x halt s hs
  have hT : ∀ e < 2, ∀ p : ℤ, cycle_power_dyadic_class_weight t (fun b => x (s + 2*p + 1) (2*b+e)) =
      (Finset.range (2^t)).sum (fun b => (x (s + 2*p + 1) (2*b+e)).toNat) := fun e he p =>
    cycle_power_dyadic_alternating_half_tight t (by omega) x htight hexact halt _ (htrue p) e he
  have hL := cycle_power_dyadic_defective_halves_lower t ht x hexact halt hpart s hs
  have hC := cycle_power_dyadic_defective_halves_cover t ht x hcover halt hpart s hs
  have hN := cycle_power_dyadic_defective_halves_count t ht x hexact hcount halt hpart s hs
  have h1t : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · simpa using hT 0 (by norm_num)
  · simpa using hL 0 (by norm_num)
  · exact cycle_power_dyadic_defective_halves_top_even t ht x hexact halt hpart s hs
  · simpa using hC 0 (by norm_num)
  · simpa using hN 0 (by norm_num)
  · exact hT 1 (by norm_num)
  · exact hL 1 (by norm_num)
  · exact cycle_power_dyadic_defective_halves_top_odd t ht x hexact halt hpart s hs
  · exact hC 1 (by norm_num)
  · intro v
    have := hN 1 (by norm_num) v
    rwa [Nat.sub_add_cancel h1t] at this
