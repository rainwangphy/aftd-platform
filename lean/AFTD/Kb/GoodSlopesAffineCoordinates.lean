import AFTD.Prelude

/-!
# good_slopes_affine_coordinates

Topic: algebra   Node: aa0ffbeff162

Provenance: helper lemma. Affine normalization for the finite-field direction argument in OP-1027.

Coordinates in the affine basis determined by three points, using the inverse of their two-by-two difference matrix.
-/

def good_slopes_affine_coordinates {K : Type*} [Field K]
    (u v w z : K × K) : K × K :=
  let dxv := v.1-u.1
  let dyv := v.2-u.2
  let dxw := w.1-u.1
  let dyw := w.2-u.2
  let det := dxv*dyw-dxw*dyv
  ((dyw*(z.1-u.1)-dxw*(z.2-u.2))/det,
   (dxv*(z.2-u.2)-dyv*(z.1-u.1))/det)
