import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_153_positive_quadratic_eventually_strict_mono

Topic: elementary_number_theory   Node: c0d4b8242ba8

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

A degree-2 integer polynomial taking positive values on all positive integers has positive leading coefficient and is eventually strictly increasing on the positive integers: there is M such that for all M ≤ n < m one has g(n) < g(m). Consequently, past M the values g(n) are pairwise distinct, the forbidden-difference set h(ℕ⁺) meets {1, ..., N} in at most as many elements as the index range {n : 1 ≤ n, g(n) ≤ N}, and the map n ↦ g(n) can be inverted.
-/

/-- A degree-2 polynomial that is positive on the positive integers is eventually strictly increasing there (so its value set is thin and its values past a threshold are distinct). -/
theorem op_153_positive_quadratic_eventually_strict_mono (g : Polynomial ℤ) (hdeg : g.degree = 2)
    (hpos : ∀ n : ℕ, 0 < n → 0 < g.eval (n : ℤ)) :
    ∃ M : ℕ, ∀ n m : ℕ, M ≤ n → n < m → g.eval (n : ℤ) < g.eval (m : ℤ) := by
  have hnd : g.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  -- Expansion of `g` at an integer point.
  have hexp : ∀ x : ℤ, g.eval x = g.coeff 2 * x^2 + g.coeff 1 * x + g.coeff 0 := by
    intro x
    rw [Polynomial.eval_eq_sum_range, hnd]
    simp [Finset.sum_range_succ]
    ring
  -- The leading coefficient (which is `g.coeff 2`) is nonzero.
  have ha_ne : g.coeff 2 ≠ 0 := by
    have hg0 : g ≠ 0 := by
      intro h
      rw [h, Polynomial.degree_zero] at hdeg
      exact absurd hdeg (by simp)
    rw [← hnd, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hg0
  -- Positivity on the positive integers forces a positive leading coefficient: an explicit
  -- large argument makes the polynomial negative otherwise.
  have ha_pos : 0 < g.coeff 2 := by
    rcases lt_or_gt_of_ne ha_ne with hneg | hgt
    · exfalso
      obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (g.coeff 1).natAbs + (g.coeff 0).natAbs + 2 := ⟨_, rfl⟩
      have hnpos : 0 < n := by omega
      have hlt := hpos n hnpos
      rw [hexp] at hlt
      have hcast : (n : ℤ) = |g.coeff 1| + |g.coeff 0| + 2 := by
        simp [hn]
      have hc : g.coeff 2 ≤ -1 := by omega
      have hN2 : (2:ℤ) ≤ (n:ℤ) := by
        rw [hcast]
        have := abs_nonneg (g.coeff 1); have := abs_nonneg (g.coeff 0); linarith
      have hNpos : (0:ℤ) ≤ (n:ℤ) := by linarith
      have hnsq : (0:ℤ) ≤ (n:ℤ)^2 := sq_nonneg _
      have hsq2 : (n:ℤ) * (|g.coeff 1| + |g.coeff 0| + 2) ≤ (n:ℤ)^2 := by
        have h : (0:ℤ) ≤ (n:ℤ) - (|g.coeff 1| + |g.coeff 0| + 2) := by
          rw [hcast]; ring_nf; exact le_refl 0
        nlinarith [mul_nonneg h hNpos]
      have e1 : g.coeff 2 * (n:ℤ)^2 ≤ -(n:ℤ)^2 := by
        nlinarith [mul_nonneg (show (0:ℤ) ≤ -1 - g.coeff 2 by linarith) hnsq]
      have e2 : g.coeff 1 * (n:ℤ) ≤ |g.coeff 1| * (n:ℤ) := by
        nlinarith [mul_le_mul_of_nonneg_right (le_abs_self (g.coeff 1)) hNpos]
      have e3 : g.coeff 0 ≤ |g.coeff 0| := le_abs_self _
      have hpc : (0:ℤ) ≤ |g.coeff 0| * ((n:ℤ) - 1) := by
        apply mul_nonneg (abs_nonneg _); linarith
      nlinarith [hlt, e1, e2, e3, hsq2, hpc, hN2]
    · exact hgt
  -- The threshold is the size of the linear coefficient plus one.
  refine ⟨(g.coeff 1).natAbs + 1, ?_⟩
  intro n m hMn hnm
  have hc1 : (1:ℤ) ≤ g.coeff 2 := by omega
  have hn : ((g.coeff 1).natAbs : ℤ) + 1 ≤ (n:ℤ) := by omega
  have hm : ((g.coeff 1).natAbs : ℤ) + 1 ≤ (m:ℤ) := by omega
  have hnmZ : (n:ℤ) < (m:ℤ) := by omega
  have habs : ((g.coeff 1).natAbs : ℤ) = |g.coeff 1| := Int.natCast_natAbs _
  have hkey : g.eval (m:ℤ) - g.eval (n:ℤ)
      = ((m:ℤ) - (n:ℤ)) * (g.coeff 2 * ((m:ℤ) + (n:ℤ)) + g.coeff 1) := by
    rw [hexp, hexp]; ring
  have hdiff : (0:ℤ) < (m:ℤ) - (n:ℤ) := by linarith
  have hsum : (0:ℤ) ≤ (m:ℤ) + (n:ℤ) := by linarith
  have hstep : (1:ℤ) * ((m:ℤ) + (n:ℤ)) ≤ g.coeff 2 * ((m:ℤ) + (n:ℤ)) :=
    mul_le_mul_of_nonneg_right hc1 hsum
  have hc1low : -|g.coeff 1| ≤ g.coeff 1 := neg_abs_le _
  have hsecond : (0:ℤ) < g.coeff 2 * ((m:ℤ) + (n:ℤ)) + g.coeff 1 := by
    nlinarith [hstep, hc1low, hn, hm, habs]
  nlinarith [hkey, hdiff, hsecond]
