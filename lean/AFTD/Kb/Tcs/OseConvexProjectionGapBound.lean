import AFTD.Prelude

/-!
# ose_convex_projection_gap_bound

Topic: algorithms   Node: fe77c6fb5103

Provenance: helper lemma. arXiv:2611.08546, Section 1.1; scalar bound for the convex-hull projection obstruction

For real n at least two, the gap between sqrt(2+2/n) and sqrt(2-2/n) is positive, at most 2/n, and after multiplying by sqrt(n) is at most 2/sqrt(n).
-/

lemma ose_convex_projection_gap_bound (n : ℝ) (hn : 2 ≤ n) :
    let a := Real.sqrt (2 - 2/n)
    let b := Real.sqrt (2 + 2/n)
    0 < b-a ∧ b-a ≤ 2/n ∧ 2 / Real.sqrt n ≥ Real.sqrt n * (b-a) := by
  dsimp only
  have hnpos : 0 < n := by linarith
  have hn0 : n ≠ 0 := ne_of_gt hnpos
  have hsmall : (1 : ℝ) ≤ 2 - 2/n := by
    have : 2/n ≤ 1 := (div_le_one hnpos).2 (by linarith)
    linarith
  have hlarge : (1 : ℝ) ≤ 2 + 2/n := by
    have h : 0 ≤ (2 : ℝ)/n := by positivity
    linarith
  have ha0 : 0 ≤ Real.sqrt (2 - 2/n) := Real.sqrt_nonneg _
  have hb0 : 0 ≤ Real.sqrt (2 + 2/n) := Real.sqrt_nonneg _
  have ha2 : (Real.sqrt (2 - 2/n))^2 = 2-2/n := Real.sq_sqrt (by linarith)
  have hb2 : (Real.sqrt (2 + 2/n))^2 = 2+2/n := Real.sq_sqrt (by linarith)
  have hnroot : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hnroot2 : (Real.sqrt n)^2 = n := Real.sq_sqrt (le_of_lt hnpos)
  have hdiv : 0 < (2 : ℝ)/n := div_pos (by norm_num) hnpos
  have ha1 : 1 ≤ Real.sqrt (2 - 2/n) := by nlinarith only [ha0, ha2, hsmall]
  have hb1 : 1 ≤ Real.sqrt (2 + 2/n) := by nlinarith only [hb0, hb2, hlarge]
  have hgap : 0 < Real.sqrt (2 + 2/n) - Real.sqrt (2 - 2/n) := by nlinarith only [ha0, hb0, ha2, hb2, hdiv]
  have hprod : (Real.sqrt (2 + 2/n) - Real.sqrt (2 - 2/n)) *
      (Real.sqrt (2 + 2/n) + Real.sqrt (2 - 2/n)) = 4/n := by
    calc
      _ = (Real.sqrt (2 + 2/n))^2 - (Real.sqrt (2 - 2/n))^2 := by ring
      _ = (2+2/n) - (2-2/n) := by rw [hb2,ha2]
      _ = 4/n := by ring
  have hfour : (4 : ℝ)/n = 2 * (2/n) := by ring
  have hbound : Real.sqrt (2 + 2/n) - Real.sqrt (2 - 2/n) ≤ 2/n := by
    nlinarith only [hprod, hfour, mul_nonneg (le_of_lt hgap)
      (show 0 ≤ Real.sqrt (2 + 2/n) + Real.sqrt (2 - 2/n) - 2 by linarith)]
  refine ⟨hgap, hbound, ?_⟩
  have hnmul : Real.sqrt n * Real.sqrt n = n := by nlinarith only [hnroot2]
  have hh : Real.sqrt n * (Real.sqrt (2 + 2/n) - Real.sqrt (2 - 2/n)) ≤
      Real.sqrt n * (2/n) := mul_le_mul_of_nonneg_left hbound (le_of_lt hnroot)
  have heq : Real.sqrt n * (2/n) = 2 / Real.sqrt n := by
    field_simp [hn0, ne_of_gt hnroot]
    nlinarith only [hnroot2]
  linarith
