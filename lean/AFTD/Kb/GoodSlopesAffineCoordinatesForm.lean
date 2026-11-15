import AFTD.Prelude
import AFTD.Kb.GoodSlopesAffineCoordinates

/-!
# good_slopes_affine_coordinates_form

Topic: algebra   Node: 50ba4b194de3

Provenance: helper lemma. Affine normalization for the finite-field direction argument in OP-1027.

The original slope form equals the affine-basis constant plus the two basis-direction coefficients times the affine coordinates.
-/

set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

theorem good_slopes_affine_coordinates_form {K : Type*} [Field K]
    (u v w z : K × K) (a : K)
    (hd : (v.1-u.1)*(w.2-u.2)-(w.1-u.1)*(v.2-u.2) ≠ 0) :
    z.2+a*z.1 = u.2+a*u.1 +
      (v.2-u.2+a*(v.1-u.1))*(good_slopes_affine_coordinates u v w z).1 +
      (w.2-u.2+a*(w.1-u.1))*(good_slopes_affine_coordinates u v w z).2 := by
  have hx : (good_slopes_affine_coordinates u v w z).1 * ((v.1-u.1)*(w.2-u.2)-(w.1-u.1)*(v.2-u.2)) =
      (w.2-u.2)*(z.1-u.1)-(w.1-u.1)*(z.2-u.2) := by
    dsimp [good_slopes_affine_coordinates]
    exact div_mul_cancel₀ _ hd
  have hy : (good_slopes_affine_coordinates u v w z).2 * ((v.1-u.1)*(w.2-u.2)-(w.1-u.1)*(v.2-u.2)) =
      (v.1-u.1)*(z.2-u.2)-(v.2-u.2)*(z.1-u.1) := by
    dsimp [good_slopes_affine_coordinates]
    exact div_mul_cancel₀ _ hd
  apply (mul_right_inj' hd).mp
  linear_combination -(v.2-u.2+a*(v.1-u.1))*hx - (w.2-u.2+a*(w.1-u.1))*hy
