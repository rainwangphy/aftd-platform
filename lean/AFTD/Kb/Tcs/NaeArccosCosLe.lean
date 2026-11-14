import AFTD.Prelude

/-!
# nae_arccos_cos_le

Topic: quantum   Node: c07c0533f2ba

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For every nonnegative x, arccos(cos x) ≤ x.
-/

theorem nae_arccos_cos_le (x : ℝ) (hx : 0 ≤ x) : Real.arccos (Real.cos x) ≤ x := by
  by_cases h : x ≤ Real.pi
  · rw [Real.arccos_cos hx h]
  · exact le_trans (Real.arccos_le_pi _) (le_of_not_ge h)
