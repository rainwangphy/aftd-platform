import AFTD.Prelude
import AFTD.Kb.Tcs.K9AffineTriangle

/-!
# k9_affine_triangles_diff_color_inter_card

Topic: graphs   Node: 0868188690d1

Provenance: helper lemma. arXiv:2611.06362 Lemma 2.1

For any two distinct colours `c₁, c₂ : Fin 4` with `c₁ ≠ c₂` and any lines `j₁, j₂ : ZMod 3`, the intersection of `k9_affine_triangle c₁ j₁` and `k9_affine_triangle c₂ j₂` has cardinality 1.
-/

/-- Any two monochromatic triangles of different colours intersect in exactly one vertex. -/
theorem k9_affine_triangles_diff_color_inter_card (c₁ c₂ : Fin 4) (j₁ j₂ : ZMod 3) (hc : c₁ ≠ c₂) :
    ((k9_affine_triangle c₁ j₁) ∩ (k9_affine_triangle c₂ j₂)).card = 1 := by
  revert c₁ c₂ j₁ j₂ hc
  decide
