import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerSumRangeDouble
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.CyclePowerDyadicAlternatingHalfTight

/-!
# cycle_power_dyadic_alternating_half_model

Topic: combinatorics   Node: babe4890e762

Provenance: helper lemma. Research thread RT-1, OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Session 2026-11-06: a no-island route that needs only alternation and endpoint-only classes, not the consecutive-bit pairing (the pairing of the middle offsets is non-local, exp 17235).

Half models. In a tight, exactly dyadically covered, fully covered integer Boolean class model at exponent m+1 (m ≥ 2) with m+2 active classes per vertex, where bit 1 alternates (x (p+1) 1 = !x p 1) and every class without bit 1 consists of its two endpoints only, fix a root s with bit 1 and a parity e < 2. Then the classes rooted at 2q+s, restricted to their offsets of parity e and halved (q, b ↦ x (2q+s) (2b+e)), form a tight, exactly dyadically covered, fully covered model at exponent m with m+1 active classes per vertex.
-/

theorem cycle_power_dyadic_alternating_bit_one_parity (x : ℤ → ℕ → Bool)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1) (s : ℤ) (hs : x s 1 = true) :
    ∀ q : ℤ, x (2*q+s) 1 = true ∧ x (2*q+s+1) 1 = false := by
  have step : ∀ q : ℤ, x (2*(q+1)+s) 1 = x (2*q+s) 1 := by
    intro q
    have e : 2*(q+1)+s = (2*q+s+1)+1 := by ring
    rw [e, halt, halt, Bool.not_not]
  have h1 : ∀ q : ℤ, x (2*q+s) 1 = true := by
    intro q
    induction q using Int.induction_on with
    | zero => simpa using hs
    | succ k ih => rw [step]; exact ih
    | pred k ih =>
      have := step (-(k:ℤ)-1)
      rw [show -(k:ℤ)-1+1 = -(k:ℤ) by ring] at this
      rw [← this]; exact ih
  intro q
  refine ⟨h1 q, ?_⟩
  rw [halt, h1 q]; rfl

theorem cycle_power_dyadic_alternating_half_count (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < (m+1), ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(m+1)-2^j)).toNat) = 1)
    (hcount : ∀ v : ℤ, (Finset.range (2^(m+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (m+1)+1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(m+1) - 1 → x p j = false)
    (s : ℤ) (hs : x s 1 = true) (e : ℕ) (he : e < 2) :
    ∀ v : ℤ, (Finset.range (2^m)).sum (fun a =>
      (x (2*(v-(a : ℤ))+s) (2*a+e)).toNat) = m+1 := by
  intro v
  have hendp := cycle_power_dyadic_exact_endpoints (m+1) (by omega) x hexact
  have hpar := cycle_power_dyadic_alternating_bit_one_parity x halt s hs
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
  have hm2 : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) hm
  have hc := hcount (2 * v + s + e)
  rw [hpow, cycle_power_sum_range_double, Finset.sum_add_distrib] at hc
  interval_cases e
  · -- even offsets are the half; odd offsets are endpoint-only classes
    have hodd : (Finset.range (2 ^ m)).sum (fun i =>
        (x (2 * v + s + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1)).toNat) = 1 := by
      rw [Finset.sum_eq_single (2 ^ m - 1)]
      · have hr : 2 * (2 ^ m - 1) + 1 = 2 * 2 ^ m - 1 := by omega
        rw [hr]
        have := (hendp (2 * v + s + ((0:ℕ):ℤ) - ((2 * 2 ^ m - 1 : ℕ) : ℤ))).2
        rw [hpow] at this
        rw [this]; rfl
      · intro i hi hne
        have hi' := Finset.mem_range.mp hi
        have hroot : 2 * v + s + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ) = 2 * (v - i - 1) + s + 1 := by
          push_cast; ring
        rw [hroot, hend _ (hpar (v - i - 1)).2 (2 * i + 1) (by omega) (by omega)]
        rfl
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    have heven : (Finset.range (2 ^ m)).sum (fun i =>
        (x (2 * v + s + ((0:ℕ):ℤ) - ((2 * i : ℕ) : ℤ)) (2 * i)).toNat) =
        (Finset.range (2^m)).sum (fun a => (x (2*(v-(a : ℤ))+s) (2*a+0)).toNat) := by
      apply Finset.sum_congr rfl
      intro i _
      have hroot : 2 * v + s + ((0:ℕ):ℤ) - ((2 * i : ℕ) : ℤ) = 2 * (v - i) + s := by push_cast; ring
      rw [hroot, Nat.add_zero]
    omega
  · have heven : (Finset.range (2 ^ m)).sum (fun i =>
        (x (2 * v + s + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ)) (2 * i)).toNat) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp only [Nat.mul_zero, Nat.cast_zero, sub_zero]
        rw [(hendp _).1]; rfl
      · intro i hi hne
        have hi' := Finset.mem_range.mp hi
        have hroot : 2 * v + s + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ) = 2 * (v - i) + s + 1 := by
          push_cast; ring
        rw [hroot, hend _ (hpar (v - i)).2 (2 * i) (by omega) (by omega)]
        rfl
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    have hodd : (Finset.range (2 ^ m)).sum (fun i =>
        (x (2 * v + s + ((1:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1)).toNat) =
        (Finset.range (2^m)).sum (fun a => (x (2*(v-(a : ℤ))+s) (2*a+1)).toNat) := by
      apply Finset.sum_congr rfl
      intro i _
      have hroot : 2 * v + s + ((1:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ) = 2 * (v - i) + s := by push_cast; ring
      rw [hroot]
    omega

theorem cycle_power_dyadic_alternating_half_cover (m : ℕ) (x : ℤ → ℕ → Bool)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(m+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(m+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(m+1) - 1 → x p j = false)
    (s : ℤ) (hs : x s 1 = true) (e : ℕ) (he : e < 2) :
    ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (2*(v-(a : ℤ))+s) (2*a+e) = true ∧
        x (2*(v-(a : ℤ))+s) (2*(a+d)+e) = true := by
  intro d hd hdm v
  have hpar := cycle_power_dyadic_alternating_bit_one_parity x halt s hs
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
  obtain ⟨a, ha, h1, h2⟩ := hcover (2 * d) (by omega) (by omega) (2 * v + s + e)
  rcases Nat.even_or_odd' a with ⟨a', rfl | rfl⟩ <;> interval_cases e
  · refine ⟨a', by omega, ?_, ?_⟩
    · have hr : 2 * v + s + ((0:ℕ):ℤ) - ((2 * a' : ℕ) : ℤ) = 2 * (v - a') + s := by push_cast; ring
      rw [hr] at h1; simpa using h1
    · have hr : 2 * v + s + ((0:ℕ):ℤ) - ((2 * a' : ℕ) : ℤ) = 2 * (v - a') + s := by push_cast; ring
      rw [hr, show 2 * a' + 2 * d = 2 * (a' + d) by ring] at h2; simpa using h2
  · exfalso
    have hr : 2 * v + s + ((1:ℕ):ℤ) - ((2 * a' : ℕ) : ℤ) = 2 * (v - a') + s + 1 := by push_cast; ring
    rw [hr] at h1 h2
    rw [hend _ (hpar _).2 (2 * a' + 2 * d) (by omega) (by omega)] at h2
    exact Bool.false_ne_true h2
  · exfalso
    have hr : 2 * v + s + ((0:ℕ):ℤ) - ((2 * a' + 1 : ℕ) : ℤ) = 2 * (v - a' - 1) + s + 1 := by
      push_cast; ring
    rw [hr] at h1 h2
    rw [hend _ (hpar _).2 (2 * a' + 1) (by omega) (by omega)] at h1
    exact Bool.false_ne_true h1
  · refine ⟨a', by omega, ?_, ?_⟩
    · have hr : 2 * v + s + ((1:ℕ):ℤ) - ((2 * a' + 1 : ℕ) : ℤ) = 2 * (v - a') + s := by push_cast; ring
      rw [hr] at h1; simpa using h1
    · have hr : 2 * v + s + ((1:ℕ):ℤ) - ((2 * a' + 1 : ℕ) : ℤ) = 2 * (v - a') + s := by push_cast; ring
      rw [hr, show 2 * a' + 1 + 2 * d = 2 * (a' + d) + 1 by ring] at h2; exact h2

theorem cycle_power_dyadic_alternating_half_exact (m : ℕ) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < (m+1), ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(m+1)-2^j)).toNat) = 1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(m+1) - 1 → x p j = false)
    (s : ℤ) (hs : x s 1 = true) (e : ℕ) (he : e < 2) :
    ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (2*(v-(a : ℤ))+s) (2*a+e) && x (2*(v-(a : ℤ))+s) (2*(a+2^m-2^j)+e)).toNat) = 1 := by
  intro j hj v
  have hpar := cycle_power_dyadic_alternating_bit_one_parity x halt s hs
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
  have hpj : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; omega
  have hjm : 2 ^ (j + 1) ≤ 2 ^ m := Nat.pow_le_pow_right (by decide) (by omega)
  have hj1 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
  have h := hexact (j + 1) (by omega) (2 * v + s + e)
  rw [hpj, cycle_power_sum_range_double, Finset.sum_add_distrib] at h
  interval_cases e
  · have hz : (Finset.range (2 ^ j)).sum (fun i =>
        (x (2 * v + s + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1) &&
          x (2 * v + s + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ)) (2 * i + 1 + 2 ^ (m + 1) - 2 * 2 ^ j)).toNat) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hr : 2 * v + s + ((0:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ) = 2 * (v - i - 1) + s + 1 := by
        push_cast; ring
      rw [hr, hend _ (hpar _).2 (2 * i + 1) (by omega) (by omega)]
      rfl
    rw [hz, Nat.add_zero] at h
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hr : 2 * v + s + ((0:ℕ):ℤ) - ((2 * i : ℕ) : ℤ) = 2 * (v - i) + s := by push_cast; ring
    have ho : 2 * i + 2 ^ (m + 1) - 2 * 2 ^ j = 2 * (i + 2 ^ m - 2 ^ j) + 0 := by omega
    rw [hr, ho, Nat.add_zero]
  · have hz : (Finset.range (2 ^ j)).sum (fun i =>
        (x (2 * v + s + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ)) (2 * i) &&
          x (2 * v + s + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ)) (2 * i + 2 ^ (m + 1) - 2 * 2 ^ j)).toNat) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hi' := Finset.mem_range.mp hi
      have hr : 2 * v + s + ((1:ℕ):ℤ) - ((2 * i : ℕ) : ℤ) = 2 * (v - i) + s + 1 := by
        push_cast; ring
      rw [hr, hend _ (hpar _).2 (2 * i + 2 ^ (m + 1) - 2 * 2 ^ j) (by omega) (by omega)]
      simp
    rw [hz, Nat.zero_add] at h
    refine Eq.trans ?_ h
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have hr : 2 * v + s + ((1:ℕ):ℤ) - ((2 * i + 1 : ℕ) : ℤ) = 2 * (v - i) + s := by push_cast; ring
    have ho : 2 * i + 1 + 2 ^ (m + 1) - 2 * 2 ^ j = 2 * (i + 2 ^ m - 2 ^ j) + 1 := by omega
    rw [hr, ho]

theorem cycle_power_dyadic_alternating_half_model (m : ℕ) (hm : 2 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (m+1) (x p) =
      (Finset.range (2^(m+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < (m+1), ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(m+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(m+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(m+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(m+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (m+1)+1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(m+1) - 1 → x p j = false)
    (s : ℤ) (hs : x s 1 = true) (e : ℕ) (he : e < 2) :
    (∀ q : ℤ, cycle_power_dyadic_class_weight m (fun b => x (2*q+s) (2*b+e)) =
      (Finset.range (2^m)).sum (fun b => (x (2*q+s) (2*b+e)).toNat)) ∧
    (∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (2*(v-(a : ℤ))+s) (2*a+e) && x (2*(v-(a : ℤ))+s) (2*(a+2^m-2^j)+e)).toNat) = 1) ∧
    (∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (2*(v-(a : ℤ))+s) (2*a+e) = true ∧
        x (2*(v-(a : ℤ))+s) (2*(a+d)+e) = true) ∧
    (∀ v : ℤ, (Finset.range (2^m)).sum (fun a =>
      (x (2*(v-(a : ℤ))+s) (2*a+e)).toNat) = m+1) := by
  have hpar := cycle_power_dyadic_alternating_bit_one_parity x halt s hs
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q
    exact cycle_power_dyadic_alternating_half_tight m (by omega) x htight hexact halt (2*q+s) (hpar q).1 e he
  · exact cycle_power_dyadic_alternating_half_exact m x hexact halt hend s hs e he
  · exact cycle_power_dyadic_alternating_half_cover m x hcover halt hend s hs e he
  · exact cycle_power_dyadic_alternating_half_count m (by omega) x hexact hcount halt hend s hs e he
