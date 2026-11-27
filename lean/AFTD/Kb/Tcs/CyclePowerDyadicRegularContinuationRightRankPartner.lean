import AFTD.Prelude

/-!
# cycle_power_dyadic_regular_continuation_right_rank_partner

Topic: combinatorics   Node: 8c9d587d708f

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there); it concerns the integer Boolean class models that optimal (m+1)-layer covers give. Partial result towards the stated cycle_power_dyadic_regular_continuation_right: the offsets D - 2^i of the class at p0+1.

Part of the rightward continuation, for every exponent t+1 ≥ 2, from exactness alone. In an exactly dyadically covered integer Boolean class model at exponent t+1 (D = 2^(t+1)), suppose that for every root r with p0 - 3·2^t ≤ r ≤ p0: if p0 - r is even, the class rooted at r contains offset 1 and its offsets come in consecutive pairs (2i and 2i+1 both in or both out, i < 2^t); if p0 - r is odd, that class consists of its two endpoints only. Then for every rank 1 ≤ i ≤ t the class rooted at p0+1 does not contain offset D - 2^i.
-/

theorem cycle_power_dyadic_regular_continuation_right_rank_partner (t : ℕ) (ht : 1 ≤ t)
    (x : ℤ → ℕ → Bool)
    (hexact : ∀ i < t+1, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^i)).toNat) = 1)
    (p0 : ℤ)
    (hreg : ∀ r : ℤ, p0 - 3*2^t ≤ r → r ≤ p0 →
      ((p0 - r) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^t, x r (2*i) = x r (2*i+1)) ∧
      ((p0 - r) % 2 = 1 → ∀ a, 0 < a → a < 2^(t+1) - 1 → x r a = false)) :
    ∀ i, 1 ≤ i → i ≤ t → x (p0+1) (2^(t+1) - 2^i) = false := by
  intro i hi1 hit
  obtain ⟨T, hT⟩ : ∃ T : ℕ, T = 2^t := ⟨_, rfl⟩
  have hD : (2:ℕ)^(t+1) = 2*T := by rw [hT, pow_succ]; ring
  have hTz : ((2:ℤ))^t = (T:ℤ) := by rw [hT]; push_cast; rfl
  obtain ⟨I, hI⟩ : ∃ I : ℕ, I = 2^i := ⟨_, rfl⟩
  have hIT : I ≤ T := by rw [hI, hT]; exact Nat.pow_le_pow_right (by norm_num) hit
  have hI2 : 2 ∣ I := by
    rw [hI]; exact dvd_pow_self 2 (by omega)
  have hIpos : 2 ≤ I := by
    rw [hI]; calc 2 = 2^1 := by norm_num
      _ ≤ 2^i := Nat.pow_le_pow_right (by norm_num) hi1
  have hx : ∀ (q q' : ℤ) (a a' : ℕ), q = q' → a = a' → x q a = x q' a' := by
    intro q q' a a' h1 h2; rw [h1, h2]
  have hends : ∀ v : ℤ, x v 0 = true := by
    intro v
    have h := hexact 0 (by omega) v
    simp only [pow_zero, Finset.range_one, Finset.sum_singleton, Nat.cast_zero, sub_zero,
      Nat.zero_add] at h
    revert h
    generalize x v 0 = u
    generalize x v (2^(t+1) - 1) = w
    cases u <;> cases w <;> simp
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, I = J + 1 := ⟨I - 1, by omega⟩
  have h0 := hexact i (by omega) p0
  have h1 := hexact i (by omega) (p0+1)
  rw [← hI, hJ, Finset.sum_range_succ] at h0
  rw [← hI, hJ, Finset.sum_range_succ'] at h1
  -- the last term at p0 vanishes: root p0 - J has odd type and J is interior
  have hlast : (x (p0 - (J:ℤ)) J && x (p0 - (J:ℤ)) (J + 2^(t+1) - (J+1))).toNat = 0 := by
    have hr := hreg (p0 - (J:ℤ)) (by rw [hTz]; omega) (by omega)
    rw [hr.2 (by omega) J (by omega) (by omega)]
    rfl
  have hfirst : (x (p0 + 1 - ((0:ℕ):ℤ)) 0 && x (p0 + 1 - ((0:ℕ):ℤ)) (0 + 2^(t+1) - (J+1))).toNat =
      (x (p0+1) (2^(t+1) - 2^i)).toNat := by
    rw [hx _ (p0+1) 0 0 (by simp) rfl, hends,
      hx (p0 + 1 - ((0:ℕ):ℤ)) (p0+1) (0 + 2^(t+1) - (J+1)) (2^(t+1) - 2^i) (by simp) (by omega)]
    rfl
  have hmid : (Finset.range J).sum (fun a =>
        (x (p0 + 1 - ((a+1 : ℕ) : ℤ)) (a+1) &&
          x (p0 + 1 - ((a+1 : ℕ) : ℤ)) (a + 1 + 2^(t+1) - (J+1))).toNat) =
      (Finset.range J).sum (fun a =>
        (x (p0 - (a : ℤ)) a && x (p0 - (a : ℤ)) (a + 2^(t+1) - (J+1))).toNat) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have haJ := Finset.mem_range.mp ha
    have hr := hreg (p0 - (a:ℤ)) (by rw [hTz]; omega) (by omega)
    rw [hx (p0 + 1 - ((a+1 : ℕ) : ℤ)) (p0 - (a:ℤ)) (a+1) (a+1) (by push_cast; ring) rfl,
      hx (p0 + 1 - ((a+1 : ℕ) : ℤ)) (p0 - (a:ℤ)) (a + 1 + 2^(t+1) - (J+1))
        (a + 2^(t+1) - (J+1) + 1) (by push_cast; ring) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one a with hpar | hpar
    · have hev := (hr.1 (by omega)).2
      have e1 := hev (a/2) (by rw [← hT]; omega)
      have e2 := hev ((a + 2^(t+1) - (J+1))/2) (by rw [← hT]; omega)
      rw [hx _ _ (a+1) (2*(a/2)+1) rfl (by omega), ← e1,
        hx _ _ (a + 2^(t+1) - (J+1) + 1) (2*((a + 2^(t+1) - (J+1))/2)+1) rfl (by omega), ← e2,
        hx _ _ (2*(a/2)) a rfl (by omega),
        hx _ _ (2*((a + 2^(t+1) - (J+1))/2)) (a + 2^(t+1) - (J+1)) rfl (by omega)]
    · rw [hr.2 (by omega) (a+1) (by omega) (by omega), hr.2 (by omega) a (by omega) (by omega)]
      simp
  rw [hlast] at h0
  rw [hfirst, hmid] at h1
  have hfin : (x (p0+1) (2^(t+1) - 2^i)).toNat = 0 := by omega
  revert hfin
  generalize x (p0+1) (2^(t+1) - 2^i) = w
  cases w <;> simp
