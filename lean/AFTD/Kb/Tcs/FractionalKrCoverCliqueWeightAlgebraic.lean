import AFTD.Prelude

/-!
# fractional_kr_cover_clique_weight_algebraic

Topic: graphs   Node: 23329e512e5c

Provenance: helper lemma. arXiv:2610.41371 Lemma 3.2

For nonzero rational r with r ≠ 1 and any rational j, 2/(r(r-1)) * (j(j-1)/2) + j(r-j)/(r-1) equals 1 + (j-1)(r-j)/r.
-/

/-- Algebraic identity for the weight sum of an r-clique intersecting K_a in j vertices. -/
theorem fractional_kr_cover_clique_weight_algebraic (r j : ℚ) (hr : r ≠ 0) (hr1 : r - 1 ≠ 0) :
    2 / (r * (r - 1)) * (j * (j - 1) / 2) + j * (r - j) / (r - 1) =
    1 + (j - 1) * (r - j) / r := by
  field_simp
  ring
