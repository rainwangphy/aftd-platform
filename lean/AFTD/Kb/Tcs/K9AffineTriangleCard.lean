import AFTD.Prelude
import AFTD.Kb.Tcs.K9AffineTriangle

/-!
# k9_affine_triangle_card

Topic: graphs   Node: dc7e3cd9baf1

Provenance: helper lemma. arXiv:2611.06362 Section 2.1

For every colour `c : Fin 4` and line `j : ZMod 3`, the monochromatic triangle `k9_affine_triangle c j` has cardinality 3.
-/

/-- Each monochromatic triangle in the affine-plane four-colouring of K9 has three vertices. -/
theorem k9_affine_triangle_card (c : Fin 4) (j : ZMod 3) : (k9_affine_triangle c j).card = 3 := by
  revert c j
  decide
