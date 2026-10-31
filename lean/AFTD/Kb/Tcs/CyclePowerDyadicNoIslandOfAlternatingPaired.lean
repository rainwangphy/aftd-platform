import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightCongr
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightDilate
import AFTD.Kb.Tcs.CyclePowerSumRangeDouble
import AFTD.Kb.Tcs.CyclePowerAlternatingPairedCompressionCount
import AFTD.Kb.Tcs.CyclePowerAlternatingPairedCompressionCover
import AFTD.Kb.Tcs.CyclePowerAlternatingPairedCompressionExactSum

/-!
# cycle_power_dyadic_no_island_of_alternating_paired

Topic: combinatorics   Node: 0e1f8d1dc659

Provenance: helper lemma. Research thread RT-1, OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Experiment 10383: the alternating-paired structure is forced at the centre of the window [-2D, 2D] of the layer-free model for m = 3, 4, 5 (D = 2^m), not at radius 1.5 D.

Uniform induction step for the no-island class shape. Let m ≥ 1 and suppose every tight, exactly dyadically covered, fully ordinarily covered integer Boolean class model at exponent m with exactly m+1 active classes at each vertex has no island (a < b < c < 2^m, bit a missing and bit b selected force bit c selected). Let x be such a model at exponent m+1 (m+2 active classes per vertex) with the alternating-paired structure: x (p+1) 1 = !(x p 1) for all p; a class with bit 1 missing has no inner bit (0 < j < 2^(m+1) - 1); a class with bit 1 selected has x p (2j) = x p (2j+1) for all j < 2^m. Then x has no island either.
-/

theorem cycle_power_dyadic_no_island_of_alternating_paired (m : ℕ) (hm : 1 ≤ m)
    (hshape : ∀ (y : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight m (y p) =
        (Finset.range (2^m)).sum (fun a => (y p a).toNat)) →
      (∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^m-d ∧ y (v-(a : ℤ)) a = true ∧
          y (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^m)).sum (fun a =>
        (y (v-(a : ℤ)) a).toNat) = m+1) →
      ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
        y p a = false → y p b = true → y p c = true)
    (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (m+1) (x p) =
      (Finset.range (2^(m+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < m+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(m+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(m+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(m+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(m+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (m+1)+1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(m+1) - 1 → x p j = false)
    (hpair : ∀ p : ℤ, x p 1 = true → ∀ j < 2^m, x p (2*j) = x p (2*j+1)) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(m+1) →
      x p a = false → x p b = true → x p c = true := open Finset in by
  set h := 2 ^ m with hh
  have hpos : 0 < h := Nat.two_pow_pos m
  have hD : 2 ^ (m+1) = 2 * h := by rw [pow_succ]; ring
  have hends : ∀ v : ℤ, x v 0 = true ∧ x v (2 * h - 1) = true := by
    intro v
    have e := hexact 0 (by omega) v
    rw [hD] at e
    simp only [pow_zero, range_one, sum_singleton, Nat.cast_zero, sub_zero, zero_add] at e
    revert e
    cases x v 0 <;> cases x v (2 * h - 1) <;> decide
  -- parity of the endpoint-only classes
  have h2 : ∀ p : ℤ, x (p + 2) 1 = x p 1 := by
    intro p
    rw [show p + 2 = (p + 1) + 1 by ring, halt (p+1), halt p, Bool.not_not]
  have hev : ∀ q : ℤ, x (2 * q) 1 = x 0 1 := by
    intro q
    induction q using Int.induction_on with
    | zero => simp
    | succ i ih => rw [show 2 * ((i:ℤ) + 1) = 2 * i + 2 by ring, h2, ih]
    | pred i ih =>
      rw [← ih, show 2 * (-(i:ℤ)) = 2 * (-(i:ℤ) - 1) + 2 by ring, h2]
  obtain ⟨s, hs⟩ : ∃ s : ℤ, ∀ q : ℤ, x (2 * q + s) 1 = false := by
    cases h0 : x 0 1
    · exact ⟨0, fun q => by rw [add_zero, hev, h0]⟩
    · exact ⟨1, fun q => by rw [halt, hev, h0]; rfl⟩
  have hs1 : ∀ q : ℤ, x (2 * q + 1 + s) 1 = true := by
    intro q
    rw [show 2 * q + 1 + s = (2 * q + s) + 1 by ring, halt, hs]; rfl
  -- the shifted model
  set x' : ℤ → ℕ → Bool := fun q j => x (q + s) j with hx'
  have hsh : ∀ v a : ℤ, v - a + s = v + s - a := fun v a => by ring
  have heven : ∀ p : ℤ, ∀ j < 2 * h, x' (2 * p) j = true ↔ j = 0 ∨ j = 2 * h - 1 := by
    intro p j hj
    simp only [hx']
    constructor
    · intro hx
      by_contra hne
      push Not at hne
      have := hend (2 * p + s) (hs p) j (by omega) (by rw [hD]; omega)
      rw [this] at hx; exact absurd hx (by decide)
    · rintro (rfl | rfl)
      · exact (hends _).1
      · exact (hends _).2
  have hpair' : ∀ q : ℤ, ∀ j < h, x' (2 * q + 1) (2 * j) = x' (2 * q + 1) (2 * j + 1) :=
    fun q j hj => hpair _ (hs1 q) j hj
  have hcover' : ∀ d, 1 ≤ d → d < 2 * h → ∀ u : ℤ,
      ∃ a < 2 * h - d, x' (u - (a : ℤ)) a = true ∧ x' (u - (a : ℤ)) (a + d) = true := by
    intro d hd1 hd u
    obtain ⟨a, ha, h1, h2⟩ := hcover d hd1 (by rw [hD]; exact hd) (u + s)
    refine ⟨a, by rw [hD] at ha; exact ha, ?_, ?_⟩
    · simp only [hx', hsh]; exact h1
    · simp only [hx', hsh]; exact h2
  set y : ℤ → ℕ → Bool := fun q i => x' (2 * q + 1) (2 * i) with hy
  -- the class of x' at 2q+1 is the dilation of y q
  have hdil : ∀ q : ℤ, ∀ j < 2 * h, x' (2 * q + 1) j = y q (j / 2) := by
    intro q j hj
    simp only [hy]
    rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
    · rw [show j / 2 = t by omega, show 2 * t = j by omega]
    · rw [show j / 2 = t by omega, hpair' q t (by omega), show 2 * t + 1 = j by omega]
  have ytight : ∀ q, cycle_power_dyadic_class_weight m (y q) =
      (range (2 ^ m)).sum (fun a => (y q a).toNat) := by
    intro q
    change cycle_power_dyadic_class_weight m (y q) = (range h).sum (fun a => (y q a).toNat)
    have ht := htight (2 * q + 1 + s)
    have hw : cycle_power_dyadic_class_weight (m+1) (x (2 * q + 1 + s)) =
        cycle_power_dyadic_class_weight (m+1) (fun j => y q (j / 2)) := by
      apply cycle_power_dyadic_class_weight_congr
      intro i hi
      rw [hD] at hi
      exact hdil q i hi
    rw [hw, cycle_power_dyadic_class_weight_dilate m hm, hD, cycle_power_sum_range_double] at ht
    have hs2 : (range h).sum (fun i => (x (2 * q + 1 + s) (2 * i)).toNat +
        (x (2 * q + 1 + s) (2 * i + 1)).toNat) = 2 * (range h).sum (fun a => (y q a).toNat) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have e := hpair' q i (mem_range.mp hi)
      simp only [hx', hy] at e ⊢
      rw [← e]; ring
    rw [hs2] at ht
    omega
  have ycount : ∀ v : ℤ, (range (2 ^ m)).sum (fun a => (y (v - (a : ℤ)) a).toNat) = m + 1 := by
    intro v
    have e := cycle_power_alternating_paired_compression_count h hpos x' heven v
    have c := hcount (2 * v + 1 + s)
    rw [hD] at c
    have c' : (range (2 * h)).sum (fun j => (x' (2 * v + 1 - (j : ℤ)) j).toNat) = m + 1 + 1 := by
      simp only [hx', hsh]; exact c
    have : (range h).sum (fun j => (x' (2 * (v - (j : ℤ)) + 1) (2 * j)).toNat) = m + 1 := by omega
    exact this
  have ycover : ∀ d : ℕ, 1 ≤ d → d < 2 ^ m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2 ^ m - d ∧ y (v - (a : ℤ)) a = true ∧ y (v - (a : ℤ)) (a + d) = true :=
    fun d hd1 hd v => cycle_power_alternating_paired_compression_cover h x' heven hcover' d hd1 hd v
  have yexact : ∀ j < m, ∀ v : ℤ, (range (2 ^ j)).sum (fun a =>
      (y (v - (a : ℤ)) a && y (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j)).toNat) = 1 := by
    intro j hj v
    have hjm : 2 ^ j < 2 ^ m := Nat.pow_lt_pow_right (by decide) hj
    have hj1 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    have e := cycle_power_alternating_paired_compression_exact_sum h (2 ^ m - 2 ^ j) (2 ^ j)
      (by omega) (by omega) x' heven v
    have c := hexact (j + 1) (by omega) (2 * v + 1 + s)
    rw [hD, hj1] at c
    have c' : (range (2 * 2 ^ j)).sum (fun a => (x' (2 * v + 1 - (a : ℤ)) a &&
        x' (2 * v + 1 - (a : ℤ)) (a + 2 * (2 ^ m - 2 ^ j))).toNat) = 1 := by
      rw [← c]
      apply sum_congr rfl
      intro a ha
      simp only [hx', hsh]
      rw [show a + 2 * (2 ^ m - 2 ^ j) = a + 2 * h - 2 * 2 ^ j by omega]
    rw [c'] at e
    rw [e]
    apply sum_congr rfl
    intro a ha
    simp only [hy]
    rw [show a + 2 ^ m - 2 ^ j = a + (2 ^ m - 2 ^ j) by omega]
  have yshape := hshape y ytight yexact ycover ycount
  -- lift back
  intro p a b c hab hbc hc ha hb
  rw [hD] at hc
  cases hp1 : x p 1
  · have := hend p hp1 b (by omega) (by rw [hD]; omega)
    rw [this] at hb; exact absurd hb (by decide)
  · set q := (p - s) / 2
    rcases (show p = 2 * q + s ∨ p = 2 * q + 1 + s by omega) with h0 | hpq
    · rw [h0, hs q] at hp1; exact absurd hp1 (by decide)
    · have hpq := hpq
      have hxy : ∀ j < 2 * h, x p j = y q (j / 2) := by
        intro j hj
        rw [← hdil q j hj, hpq]
      rw [hxy a (by omega)] at ha
      rw [hxy b (by omega)] at hb
      rw [hxy c hc]
      have hab2 : a / 2 < b / 2 := by
        rcases Nat.lt_or_ge (a / 2) (b / 2) with h' | h'
        · exact h'
        · rw [show a / 2 = b / 2 by omega, hb] at ha; exact absurd ha (by decide)
      rcases Nat.lt_or_ge (b / 2) (c / 2) with h' | h'
      · exact yshape q (a / 2) (b / 2) (c / 2) hab2 h' (by omega) ha hb
      · rw [show c / 2 = b / 2 by omega]; exact hb
