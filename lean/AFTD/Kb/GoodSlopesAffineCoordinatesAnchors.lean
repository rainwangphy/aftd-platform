import AFTD.Prelude
import AFTD.Kb.GoodSlopesAffineCoordinates

/-!
# good_slopes_affine_coordinates_anchors

Topic: algebra   Node: e8373070debd

Provenance: helper lemma. Affine normalization for the finite-field direction argument in OP-1027.

The affine-coordinate map sends the three noncollinear basis points to (0,0), (1,0), and (0,1).
-/

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

theorem good_slopes_affine_coordinates_anchors {K : Type*} [Field K]
    (u v w : K × K)
    (hd : (v.1-u.1)*(w.2-u.2)-(w.1-u.1)*(v.2-u.2) ≠ 0) :
    good_slopes_affine_coordinates u v w u = (0,0) ∧
    good_slopes_affine_coordinates u v w v = (1,0) ∧
    good_slopes_affine_coordinates u v w w = (0,1) := by
  constructor
  · apply Prod.ext <;> dsimp [good_slopes_affine_coordinates] <;> apply (div_eq_iff hd).2 <;> ring
  constructor
  · apply Prod.ext <;> dsimp [good_slopes_affine_coordinates] <;> apply (div_eq_iff hd).2 <;> ring
  · apply Prod.ext <;> dsimp [good_slopes_affine_coordinates] <;> apply (div_eq_iff hd).2 <;> ring
