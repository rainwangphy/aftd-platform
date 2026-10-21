import AFTD.Prelude
import AFTD.Kb.NumberTheory.Op153PositiveQuadraticEventuallyStrictMono
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_153_positive_quadratic_eventually_quadratic_lower_bound

Topic: elementary_number_theory   Node: 26b48f17504f

Provenance: helper lemma. step towards op_153_eventually_subexp_bound_positive_quadratic

A degree-2 integer polynomial strictly positive on positive integers satisfies $n^2 \le 2 g(n)$ for all sufficiently large positive integers $n$.
-/

/-- A degree-2 integer polynomial taking positive values on all positive integers eventually satisfies n^2 <= 2 g(n). -/
theorem op_153_positive_quadratic_eventually_quadratic_lower_bound (g : Polynomial ℤ)
    (hdeg : g.degree = 2) (hpos : ∀ n : ℕ, 0 < n → 0 < g.eval (n : ℤ)) :
    ∃ M : ℕ, ∀ n : ℕ, M ≤ n → (n : ℤ) ^ 2 ≤ 2 * g.eval (n : ℤ) := by
  have hnd : g.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hdeg
  have hexp : ∀ x : ℤ, g.eval x = g.coeff 2 * x^2 + g.coeff 1 * x + g.coeff 0 := by
    intro x
    rw [Polynomial.eval_eq_sum_range, hnd]
    simp [Finset.sum_range_succ]
    ring
  have ha_ne : g.coeff 2 ≠ 0 := by
    have hg0 : g ≠ 0 := by
      intro h
      rw [h, Polynomial.degree_zero] at hdeg
      exact absurd hdeg (by simp)
    rw [← hnd, Polynomial.coeff_natDegree]
    exact Polynomial.leadingCoeff_ne_zero.mpr hg0
  have ha_pos : 0 < g.coeff 2 := by
    rcases lt_or_gt_of_ne ha_ne with hneg | hgt
    · exfalso
      obtain ⟨n, hn⟩ : ∃ n : ℕ, n = (g.coeff 1).natAbs + (g.coeff 0).natAbs + 2 := ⟨_, rfl⟩
      have hnpos : 0 < n := by omega
      have hlt := hpos n hnpos
      rw [hexp] at hlt
      have hcast : (n : ℤ) = |g.coeff 1| + |g.coeff 0| + 2 := by simp [hn]
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
  refine ⟨2 * (g.coeff 1).natAbs + 2 * (g.coeff 0).natAbs + 1, ?_⟩
  intro n hn
  rw [hexp]
  have hc1 : (1:ℤ) ≤ g.coeff 2 := by omega
  have hbound : (2 * |g.coeff 1| + 2 * |g.coeff 0| + 1 : ℤ) ≤ (n:ℤ) := by
    have : ((2 * (g.coeff 1).natAbs + 2 * (g.coeff 0).natAbs + 1 : ℕ) : ℤ) ≤ (n : ℤ) := by
      exact Nat.cast_le.mpr hn
    push_cast at this
    exact this
  have hnpos : (0:ℤ) ≤ (n:ℤ) := by linarith [abs_nonneg (g.coeff 1), abs_nonneg (g.coeff 0), hbound]
  have hnsq : (0:ℤ) ≤ (n:ℤ)^2 := sq_nonneg _
  have hlead : (n:ℤ)^2 ≤ (2 * g.coeff 2 - 1) * (n:ℤ)^2 := by
    nlinarith [show (0:ℤ) ≤ 2 * g.coeff 2 - 2 by linarith]
  have hsq_ge : (2 * |g.coeff 1| + 1) * (n:ℤ) ≤ (n:ℤ)^2 := by
    have h : (2 * |g.coeff 1| + 1 : ℤ) ≤ (n:ℤ) := by
      linarith [abs_nonneg (g.coeff 0), hbound]
    calc
      (2 * |g.coeff 1| + 1) * (n:ℤ) ≤ (n:ℤ) * (n:ℤ) := by
        apply mul_le_mul_of_nonneg_right h hnpos
      _ = (n:ℤ)^2 := by ring
  have hlin : -2 * |g.coeff 1| * (n:ℤ) ≤ 2 * g.coeff 1 * (n:ℤ) := by
    have := neg_abs_le (g.coeff 1)
    nlinarith
  have hconst : -2 * |g.coeff 0| ≤ 2 * g.coeff 0 := by
    have := neg_abs_le (g.coeff 0)
    linarith
  have htail : 2 * |g.coeff 0| ≤ (n:ℤ) := by
    linarith [abs_nonneg (g.coeff 1), hbound]
  linarith
