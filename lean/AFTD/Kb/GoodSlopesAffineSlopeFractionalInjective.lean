import AFTD.Prelude

/-!
# good_slopes_affine_slope_fractional_injective

Topic: algebra   Node: a67577060d6e

Provenance: helper lemma. Affine direction transport in the finite-field line argument for OP-1027.

Over a field, a fractional linear slope transformation associated with a nonzero two-by-two determinant is injective wherever both denominators are nonzero.
-/

set_option maxHeartbeats 5000000

theorem good_slopes_affine_slope_fractional_injective {K : Type*} [Field K]
    (dxv dyv dxw dyw a b : K)
    (hd : dxv*dyw-dxw*dyv ≠ 0)
    (ha : dyw+a*dxw ≠ 0) (hb : dyw+b*dxw ≠ 0)
    (heq : (dyv+a*dxv)/(dyw+a*dxw) = (dyv+b*dxv)/(dyw+b*dxw)) : a = b := by
  have hc : (dyv+a*dxv)*(dyw+b*dxw) = (dyv+b*dxv)*(dyw+a*dxw) :=
    (div_eq_div_iff ha hb).mp heq
  have hm : (a-b)*(dxv*dyw-dxw*dyv) = 0 := by linear_combination hc
  exact sub_eq_zero.mp ((mul_eq_zero.mp hm).resolve_right hd)
