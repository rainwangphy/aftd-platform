import AFTD.Prelude

/-!
# fractional_kr_cover_clique_weight_ge_one

Topic: graphs   Node: 85f85874bfad

Provenance: helper lemma. arXiv:2610.41371 Lemma 3.2

For rational r > 0 and 1 ≤ j ≤ r, the quantity 1 + (j - 1)(r - j)/r is at least 1.
-/

/-- Inequality showing the clique edge weight sum is at least 1 when 1 ≤ j ≤ r. -/
theorem fractional_kr_cover_clique_weight_ge_one (r j : ℚ) (hr : 0 < r)
    (hj1 : 1 ≤ j) (hjr : j ≤ r) :
    1 ≤ 1 + (j - 1) * (r - j) / r := by
  have h1 : 0 ≤ j - 1 := by linarith
  have h2 : 0 ≤ r - j := by linarith
  have h3 : 0 ≤ (j - 1) * (r - j) := mul_nonneg h1 h2
  have h4 : 0 ≤ (j - 1) * (r - j) / r := div_nonneg h3 (le_of_lt hr)
  linarith
