import AFTD.Prelude

/-!
# two_type_proper_allocation_is_pareto_optimal

Topic: fair_division   Node: c38e62d2dae2

Provenance: helper lemma. step towards two_type_goods_simultaneous_efx_mms_pareto

In a two-type fair division instance with agents sorted by non-increasing valuation ratio p_i / q_i, every proper allocation (where no higher-index agent receives good A while a lower-index agent receives good B) is Pareto optimal.
-/

private lemma two_type_proper_allocation_is_pareto_optimal_key
    (n : ℕ) (p q : Fin n → ℝ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (h_sorted : ∀ i j : Fin n, i < j → p j * q i ≤ p i * q j)
    (m : Fin n) (D E : Fin n → ℝ)
    (hsumD : ∑ i, D i = 0) (hsumE : ∑ i, E i = 0)
    (hDpos : ∀ i, m < i → 0 ≤ D i) (hEpos : ∀ i, i < m → 0 ≤ E i)
    (hG : ∀ i, 0 ≤ p i * D i + q i * E i)
    (hstrict : ∃ i, 0 < p i * D i + q i * E i) : False := by
  let w : Fin n → ℝ := fun i => if i ≤ m then p m / p i else q m / q i
  have hwpos : ∀ i, 0 < w i := by
    intro i; by_cases hi : i ≤ m
    · simp only [w, if_pos hi]; exact div_pos (hp m) (hp i)
    · simp only [w, if_neg hi]; exact div_pos (hq m) (hq i)
  have hterm : ∀ i, (w i * p i - p m) * D i + (w i * q i - q m) * E i ≤ 0 := by
    intro i
    rcases lt_trichotomy i m with h | h | h
    · have hle : i ≤ m := le_of_lt h
      have hw : w i = p m / p i := by simp only [w, if_pos hle]
      rw [hw]
      have hDcoef : (p m / p i) * p i - p m = 0 := by
        rw [div_mul_cancel₀ _ (ne_of_gt (hp i))]; ring
      have hEcoef : (p m / p i) * q i - q m ≤ 0 := by
        have hkey : p m * q i ≤ q m * p i := by have := h_sorted i m h; nlinarith [this]
        have heq : (p m / p i) * q i = (p m * q i) / p i := by ring
        rw [heq, sub_nonpos, div_le_iff₀ (hp i)]; linarith
      rw [hDcoef, zero_mul, zero_add]
      exact mul_nonpos_of_nonpos_of_nonneg hEcoef (hEpos i h)
    · rw [h]
      have hw : w m = p m / p m := by simp only [w, if_pos (le_refl m)]
      rw [hw, div_self (ne_of_gt (hp m))]
      have hDcoef : (1:ℝ) * p m - p m = 0 := by ring
      have hEcoef : (1:ℝ) * q m - q m = 0 := by ring
      rw [hDcoef, hEcoef]; simp
    · have hlt : ¬ i ≤ m := not_le.mpr h
      have hw : w i = q m / q i := by simp only [w, if_neg hlt]
      rw [hw]
      have hEcoef : (q m / q i) * q i - q m = 0 := by
        rw [div_mul_cancel₀ _ (ne_of_gt (hq i))]; ring
      have hDcoef : (q m / q i) * p i - p m ≤ 0 := by
        have hkey : q m * p i ≤ p m * q i := by have := h_sorted m i h; nlinarith [this]
        have heq : (q m / q i) * p i = (q m * p i) / q i := by ring
        rw [heq, sub_nonpos, div_le_iff₀ (hq i)]; linarith
      rw [hEcoef, zero_mul, add_zero]
      exact mul_nonpos_of_nonpos_of_nonneg hDcoef (hDpos i h)
  have hsum_nonpos : ∑ i, ((w i * p i - p m) * D i + (w i * q i - q m) * E i) ≤ 0 :=
    Finset.sum_nonpos (fun i _ => hterm i)
  have hEq : ∑ i, w i * (p i * D i + q i * E i)
      = ∑ i, ((w i * p i - p m) * D i + (w i * q i - q m) * E i) := by
    have hpoint : ∀ i, w i * (p i * D i + q i * E i)
        = ((w i * p i - p m) * D i + (w i * q i - q m) * E i) + (p m * D i + q m * E i) := by
      intro i; ring
    simp_rw [hpoint]
    rw [Finset.sum_add_distrib]
    have hzero : ∑ i, (p m * D i + q m * E i) = 0 := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hsumD, hsumE]; ring
    rw [hzero, add_zero]
  have hLHSle : ∑ i, w i * (p i * D i + q i * E i) ≤ 0 := by rw [hEq]; exact hsum_nonpos
  have hnonneg : 0 ≤ ∑ i, w i * (p i * D i + q i * E i) :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (le_of_lt (hwpos i)) (hG i))
  have hLHS0 : ∑ i, w i * (p i * D i + q i * E i) = 0 := le_antisymm hLHSle hnonneg
  obtain ⟨i, hi⟩ := hstrict
  have hnn : ∀ j, 0 ≤ w j * (p j * D j + q j * E j) := fun j => mul_nonneg (le_of_lt (hwpos j)) (hG j)
  have hle_i : w i * (p i * D i + q i * E i) ≤ ∑ j, w j * (p j * D j + q j * E j) :=
    Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i)
  rw [hLHS0] at hle_i
  have hzi : w i * (p i * D i + q i * E i) = 0 := le_antisymm hle_i (hnn i)
  have hne : w i ≠ 0 := ne_of_gt (hwpos i)
  have hpD : p i * D i + q i * E i = 0 := by
    rcases mul_eq_zero.mp hzi with hh | hh
    · exact absurd hh hne
    · exact hh
  linarith [hi, hpD]

/-- In a two-type fair division instance with agents sorted by valuation ratio, every proper allocation is Pareto optimal. -/
theorem two_type_proper_allocation_is_pareto_optimal (n a b : ℕ) (p q : Fin n → ℝ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (h_sorted : ∀ i j : Fin n, i < j → p j * q i ≤ p i * q j)
    (x y : Fin n → ℕ) (hx : ∑ i, x i = a) (hy : ∑ i, y i = b)
    (h_proper : ∀ i j : Fin n, i < j → y i = 0 ∨ x j = 0) :
    ¬ ∃ x' y' : Fin n → ℕ, (∑ i, x' i = a) ∧ (∑ i, y' i = b) ∧
      (∀ i : Fin n, p i * (x i : ℝ) + q i * (y i : ℝ) ≤ p i * (x' i : ℝ) + q i * (y' i : ℝ)) ∧
      (∃ i : Fin n, p i * (x i : ℝ) + q i * (y i : ℝ) < p i * (x' i : ℝ) + q i * (y' i : ℝ)) := by
  rintro ⟨x', y', hx', hy', hle, hlt⟩
  have hxR : (∑ i, (x i : ℝ)) = (a:ℝ) := by rw [← hx]; push_cast; ring
  have hx'R : (∑ i, (x' i : ℝ)) = (a:ℝ) := by rw [← hx']; push_cast; ring
  have hyR : (∑ i, (y i : ℝ)) = (b:ℝ) := by rw [← hy]; push_cast; ring
  have hy'R : (∑ i, (y' i : ℝ)) = (b:ℝ) := by rw [← hy']; push_cast; ring
  set D : Fin n → ℝ := fun i => (x' i : ℝ) - (x i : ℝ) with hD
  set E : Fin n → ℝ := fun i => (y' i : ℝ) - (y i : ℝ) with hE
  have hsumD : ∑ i, D i = 0 := by
    simp only [hD]; rw [Finset.sum_sub_distrib, hx'R, hxR]; ring
  have hsumE : ∑ i, E i = 0 := by
    simp only [hE]; rw [Finset.sum_sub_distrib, hy'R, hyR]; ring
  have hG : ∀ i, 0 ≤ p i * D i + q i * E i := by
    intro i; have := hle i; simp only [hD, hE]; nlinarith [this]
  have hstrict : ∃ i, 0 < p i * D i + q i * E i := by
    obtain ⟨i, hi⟩ := hlt
    exact ⟨i, by simp only [hD, hE]; nlinarith [hi]⟩
  by_cases hex : ∃ i : Fin n, 0 < y i
  · let S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < y i)
    have hS : S.Nonempty := by
      obtain ⟨i, hi⟩ := hex
      exact ⟨i, by simp [S, hi]⟩
    let m : Fin n := S.min' hS
    have hmS : m ∈ S := Finset.min'_mem S hS
    have hm_pos : 0 < y m := by
      have h' : m ∈ Finset.univ.filter (fun i => 0 < y i) := hmS
      exact (Finset.mem_filter.mp h').2
    have hleft : ∀ i, i < m → y i = 0 := by
      intro i hi
      have hnot : ¬ (i ∈ S) := by
        intro his
        have := Finset.min'_le S i his
        omega
      have : ¬ 0 < y i := by
        intro hpos; exact hnot (by simp [S, hpos])
      omega
    have hright : ∀ j, m < j → x j = 0 := by
      intro j hj
      have := h_proper m j hj
      rcases this with h | h
      · exact absurd h (ne_of_gt hm_pos)
      · exact h
    have hDpos : ∀ i, m < i → 0 ≤ D i := by
      intro i hi
      have hx0 : x i = 0 := hright i hi
      have hnonneg : (0:ℝ) ≤ (x' i : ℝ) := by exact_mod_cast Nat.zero_le (x' i)
      simp only [hD, hx0, Nat.cast_zero]
      linarith
    have hEpos : ∀ i, i < m → 0 ≤ E i := by
      intro i hi
      have hy0 : y i = 0 := hleft i hi
      have hnonneg : (0:ℝ) ≤ (y' i : ℝ) := by exact_mod_cast Nat.zero_le (y' i)
      simp only [hE, hy0, Nat.cast_zero]
      linarith
    exact two_type_proper_allocation_is_pareto_optimal_key n p q hp hq h_sorted m D E
      hsumD hsumE hDpos hEpos hG hstrict
  · have hyzero : ∀ i, y i = 0 := by
      intro i
      have h : ¬ 0 < y i := fun hh => hex ⟨i, hh⟩
      omega
    have hb0 : b = 0 := by rw [← hy]; exact Finset.sum_eq_zero (fun i _ => hyzero i)
    have hy'zero : ∀ i, y' i = 0 := by
      intro i
      have hsum : ∑ j, y' j = 0 := by rw [hy', hb0]
      have : y' i ≤ ∑ j, y' j := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
      omega
    have hxx : ∀ i, x i ≤ x' i := by
      intro i
      have h := hle i
      rw [hyzero i, hy'zero i] at h
      simp only [Nat.cast_zero, mul_zero, add_zero] at h
      have hp' := hp i
      have h2 : (x i : ℝ) ≤ (x' i : ℝ) := by nlinarith [h, hp']
      exact_mod_cast h2
    have hall : ∀ i, x' i = x i := by
      intro i
      by_contra hc
      have hlt2 : x i < x' i := lt_of_le_of_ne (hxx i) (Ne.symm hc)
      have hsum := Finset.sum_lt_sum (fun j _ => hxx j) ⟨i, Finset.mem_univ i, hlt2⟩
      omega
    obtain ⟨i, hi⟩ := hlt
    rw [hyzero i, hy'zero i, hall i] at hi
    simp only [Nat.cast_zero, mul_zero, add_zero] at hi
    exact lt_irrefl _ hi
