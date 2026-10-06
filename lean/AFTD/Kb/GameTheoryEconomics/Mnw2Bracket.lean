import AFTD.Prelude

/-!
# mnw2_bracket

Topic: fair_division   Node: 72591deb961c

Provenance: helper lemma. step towards mnw_two_agents_welfare_le (upper bound 27/23 for the price of MNW with two agents, The Price of Fairness for Indivisible Goods, arXiv:1905.04910, Theorem 5.4; Positivstellensatz certificate found by computer)

For nonnegative reals P, r, g, d with P + r ≤ 1, r(1 − g) ≤ P(g + d) and r d ≤ P g, we have 23 r ≤ 4P + 27 g + 4 d. (Case 23P ≤ 4 is linear after two product estimates; otherwise multiply the target by P² + Pr + r² and write the product as a nonnegative combination of the hypotheses.)
-/

/-- Two-variable bracket inequality used in the two easy cases of the two-agent price-of-MNW bound. -/
theorem mnw2_bracket (P r g d : ℝ) (hP : 0 ≤ P) (hr : 0 ≤ r) (hg : 0 ≤ g) (hd : 0 ≤ d) (hPr : P + r ≤ 1) (hC : r * (1 - g) ≤ P * (g + d)) (hD : r * d ≤ P * g) : 23 * r ≤ 4 * P + 27 * g + 4 * d := by
  rcases le_total (23 * P) 4 with h | h
  · have e1 : 0 ≤ g * (1 - P - r) := mul_nonneg hg (by linarith)
    have e2 : 0 ≤ d * (4 - 23 * P) := mul_nonneg hd (by linarith)
    nlinarith
  · have hk : 0 ≤ (P ^ 2 + P * r + r ^ 2) * (4 * P + 27 * g + 4 * d - 23 * r) := by
      have e1 : 0 ≤ (27 * r + 4 * P) * (P * (g + d) - r * (1 - g)) :=
        mul_nonneg (by linarith) (by linarith)
      have e2 : 0 ≤ (23 * P - 4 * r) * (P * g - r * d) :=
        mul_nonneg (by linarith) (by linarith)
      have e3 : 0 ≤ r * (27 * r + 4 * P) * (1 - P - r) :=
        mul_nonneg (mul_nonneg hr (by linarith)) (by linarith)
      have e4 : 0 ≤ (2 * r - P) ^ 2 * (r + 4 * P) := mul_nonneg (sq_nonneg _) (by linarith)
      linear_combination e1 + e2 + e3 + e4
    rcases (show 0 ≤ P ^ 2 + P * r + r ^ 2 by positivity).eq_or_lt with h0 | h0
    · have hP0 : P = 0 := by nlinarith
      have hr0 : r = 0 := by nlinarith
      subst hP0 hr0
      linarith
    · have := (mul_nonneg_iff_of_pos_left h0).mp hk
      linarith
