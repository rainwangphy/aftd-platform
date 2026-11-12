import AFTD.Prelude

/-!
# one_strongly_euclidean_sphere_radial_bound

Topic: algorithms   Node: 5f0d16af7b1a

Provenance: helper lemma. OP-1304: radial separation estimate for the two-layer spherical extension.

If r and s are positive, s²+2rs=1, and d is at least one, then s d is at most sqrt(r²+d²)−r.
-/

theorem one_strongly_euclidean_sphere_radial_bound (r s d : ℝ) (hr : 0 < r) (hs : 0 < s)
    (hid : s^2 + 2*r*s = 1) (hd : 1 ≤ d) :
    s*d ≤ Real.sqrt (r^2 + d^2) - r := by
  have hz : 0 ≤ 2*r*s*d*(d-1) := by positivity
  have hmul := congrArg (fun x : ℝ => d^2*x) hid
  have hsq : (r+s*d)^2 ≤ r^2+d^2 := by nlinarith
  have hroot : (Real.sqrt (r^2+d^2))^2 = r^2+d^2 := Real.sq_sqrt (by positivity)
  have hrootnonneg := Real.sqrt_nonneg (r^2+d^2)
  have hp : 0 ≤ r+s*d := by positivity
  nlinarith
