import AFTD.Prelude

/-!
# ratio_add_le_max_of_nonneg

Topic: online_algorithms   Node: 6df35ca98ba9

Provenance: helper lemma. arXiv:2610.29037 Lemma 4.2 proof step (5)

For real numbers A, C, D, rho with 0 < C and 0 ≤ D, (A + rho * D) / (C + D) ≤ max (A / C) rho.
-/

/-- Mediant ratio bound: (A + rho * D) / (C + D) <= max (A / C) rho for C > 0 and D >= 0. -/
theorem ratio_add_le_max_of_nonneg (A C D rho : ℝ) (hC : 0 < C) (hD : 0 ≤ D) :
    (A + rho * D) / (C + D) ≤ max (A / C) rho := by
  have hCD : 0 < C + D := add_pos_of_pos_of_nonneg hC hD
  rw [div_le_iff₀ hCD]
  have h1 : A / C ≤ max (A / C) rho := le_max_left (A / C) rho
  have h2 : rho ≤ max (A / C) rho := le_max_right (A / C) rho
  have h3 : A ≤ max (A / C) rho * C := (div_le_iff₀ hC).mp h1
  have h4 : rho * D ≤ max (A / C) rho * D := mul_le_mul_of_nonneg_right h2 hD
  calc A + rho * D ≤ max (A / C) rho * C + max (A / C) rho * D := add_le_add h3 h4
  _ = max (A / C) rho * (C + D) := by ring
