import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsIntersectiveCompXAddC
import AFTD.Kb.NumberTheory.IsIntersective
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_153_intersective_quadratic_normalize_positive

Topic: elementary_number_theory   Node: 84839b6f9d06

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

If the eventual subexponential difference bound holds for every degree-2 intersective integer polynomial that is strictly positive on all positive integers, then it holds for every degree-2 intersective integer polynomial (no positivity hypothesis): flip the sign so that the leading coefficient is positive, then shift the argument by a constant so that the polynomial is positive on all positive integers. Both operations preserve degree-2-ness and intersective-ness, and the shifted polynomial's positive values are a subset (up to sign) of h's values on positive integers, so a set avoiding differences equal to h(n) also avoids differences equal to the shifted polynomial's values.
-/

lemma op_153_intersective_quadratic_normalize_positive_quad_pos
    (a b c x : ℤ) (ha : 1 ≤ a) (hx : 2 * |b| + 2 * |c| + 2 ≤ x) :
    0 < a * x^2 + b * x + c := by
  have hb1 : -|b| ≤ b := neg_abs_le b
  have hc1 : -|c| ≤ c := neg_abs_le c
  have hb0 : 0 ≤ |b| := abs_nonneg b
  have hc0 : 0 ≤ |c| := abs_nonneg c
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 ≤ x := by linarith
  have hxx : x * 2 ≤ x * x := by nlinarith
  have hxb : 2 * |b| * x ≤ x * x := by
    have : 2 * |b| ≤ x := by linarith
    nlinarith
  have hxc : 4 * |c| ≤ 2 * |c| * x := by nlinarith
  nlinarith

/-- Sign and translation normalisation: the eventual subexponential bound for quadratics that are positive on the positive integers implies it for all degree-2 intersective quadratics. -/
theorem op_153_intersective_quadratic_normalize_positive
    (H : ∀ (g : Polynomial ℤ), g.degree = 2 → is_intersective g →
      (∀ n : ℕ, 0 < n → 0 < g.eval (n : ℤ)) →
      ∃ c > 0, ∃ C > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A ⊆ Finset.Icc 1 N,
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ n : ℕ, 0 < n ∧ (a : ℤ) - b = g.eval (n : ℤ)) →
        (A.card : ℝ) ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ))))) :
    ∀ (h : Polynomial ℤ), h.degree = 2 → is_intersective h →
      ∃ c > 0, ∃ C > 0, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ A ⊆ Finset.Icc 1 N,
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ¬ ∃ n : ℕ, 0 < n ∧ (a : ℤ) - b = h.eval (n : ℤ)) →
        (A.card : ℝ) ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log (N : ℝ) * Real.log (Real.log (N : ℝ)))) := by
  intro h hdeg hint
  set s := if 0 < h.coeff 2 then h else -h
  have hs_eval (x : ℤ) : s.eval x = h.eval x ∨ s.eval x = -h.eval x := by
    dsimp [s]; split_ifs
    · left; rfl
    · right; simp [Polynomial.eval_neg]
  have hs_deg : s.degree = 2 := by
    dsimp [s]; split_ifs
    · exact hdeg
    · rw [Polynomial.degree_neg, hdeg]
  have hs_int : is_intersective s := by
    dsimp [s]; split_ifs
    · exact hint
    · intro m hm
      obtain ⟨n, hn⟩ := hint m hm
      refine ⟨n, ?_⟩
      have := hn.neg
      simpa [Polynomial.eval_neg] using this
  have hs_lead : 1 ≤ s.coeff 2 := by
    have hd : s.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hs_deg
    have hne : h ≠ 0 := by
      rintro rfl
      rw [Polynomial.degree_zero] at hdeg
      revert hdeg
      decide
    have hlc := Polynomial.leadingCoeff_ne_zero.mpr hne
    have h2 : h.coeff 2 = h.leadingCoeff := by
      have hd_h : h.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
      rw [← hd_h, Polynomial.coeff_natDegree]
    have h_ne_zero : h.coeff 2 ≠ 0 := by rw [h2]; exact hlc
    dsimp [s]
    split_ifs with hpos
    · exact hpos
    · rw [Polynomial.coeff_neg]
      have : h.coeff 2 < 0 := lt_of_le_of_ne (not_lt.mp hpos) h_ne_zero
      linarith
  set C₁ : ℕ := 2 * (s.coeff 1).natAbs + 2 * (s.coeff 0).natAbs + 2
  have hC₁ : (C₁ : ℤ) = 2 * |s.coeff 1| + 2 * |s.coeff 0| + 2 := by
    dsimp [C₁]
    push_cast
    rfl
  set g := s.comp (Polynomial.X + Polynomial.C (C₁ : ℤ))
  have hdeg_g : g.degree = 2 := by
    dsimp [g]
    rw [Polynomial.degree_comp]
    · rw [Polynomial.degree_X_add_C, hs_deg]
      rfl
    · rw [Polynomial.degree_X_add_C]
      decide
  have hint_g : is_intersective g := by
    dsimp [g]
    exact is_intersective_comp_X_add_C s hs_int (C₁ : ℤ)
  have hpos_g : ∀ n : ℕ, 0 < n → 0 < g.eval (n : ℤ) := by
    intro n hn
    have hd : s.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hs_deg
    have heval : g.eval (n : ℤ) =
        s.coeff 2 * ((n : ℤ) + (C₁ : ℤ))^2 + s.coeff 1 * ((n : ℤ) + (C₁ : ℤ)) + s.coeff 0 := by
      dsimp [g]
      rw [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C,
          Polynomial.eval_eq_sum_range, hd]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, mul_one, pow_one]
      ring
    rw [heval]
    apply op_153_intersective_quadratic_normalize_positive_quad_pos
      (s.coeff 2) (s.coeff 1) (s.coeff 0) ((n : ℤ) + (C₁ : ℤ)) hs_lead
    rw [hC₁]
    have : 1 ≤ (n : ℤ) := by omega
    linarith
  obtain ⟨c, hc, C, hC, N₀, hN₀⟩ := H g hdeg_g hint_g hpos_g
  refine ⟨c, hc, C, hC, N₀, fun N hN A hA h_avoid => ?_⟩
  apply hN₀ N hN A hA
  intro a ha b hb hab ⟨n, hn, heq⟩
  have heval : g.eval (n : ℤ) = s.eval ((n + C₁ : ℕ) : ℤ) := by
    dsimp [g]
    simp [Polynomial.eval_comp]
  rw [heval] at heq
  have hm_pos : 0 < n + C₁ := by omega
  have hs_ev := hs_eval ((n + C₁ : ℕ) : ℤ)
  rcases hs_ev with h1 | h2
  · rw [h1] at heq
    exact h_avoid a ha b hb hab ⟨n + C₁, hm_pos, heq⟩
  · rw [h2] at heq
    have h_symm : (b : ℤ) - a = h.eval ((n + C₁ : ℕ) : ℤ) := by
      calc (b : ℤ) - a = -((a : ℤ) - b) := by ring
      _ = -(-h.eval ((n + C₁ : ℕ) : ℤ)) := by rw [heq]
      _ = h.eval ((n + C₁ : ℕ) : ℤ) := by ring
    exact h_avoid b hb a ha (Ne.symm hab) ⟨n + C₁, hm_pos, h_symm⟩
