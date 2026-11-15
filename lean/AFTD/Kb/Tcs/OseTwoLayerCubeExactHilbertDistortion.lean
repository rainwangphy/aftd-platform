import AFTD.Prelude
import AFTD.Kb.Tcs.OseCubeHilbertAntipodalInequality
import AFTD.Kb.Tcs.OseSphericalTwoLayerHilbertDistortionUpper
import AFTD.Kb.Tcs.OseBooleanCubeGeometry
import AFTD.Kb.Tcs.EmbedsIntoHilbertWithDistortion
import AFTD.Kb.Tcs.OseBooleanCubeDistSqHamming
import AFTD.Kb.Tcs.OseHammingAntipode
import AFTD.Kb.Tcs.OseHammingFlip
import AFTD.Kb.Tcs.OseCubeScaleDistortionLower

/-!
# ose_two_layer_cube_exact_hilbert_distortion

Topic: algorithms   Node: dbaf8537c243

Provenance: original. Related work: arXiv:2611.08546, Section 6.1, two-layer cube

Let n be a natural number at least two, let r and s be positive reals with s²+2rs=1, and consider any metric on pairs (b,x) with a Boolean b and Boolean n-tuple x. For each pair x,y at Hamming distance h, assume the false-layer distance is sqrt(h), the false-to-true distance is sqrt(r²+h), and the true-layer distance is min(s*h,sqrt(h)). Then for every real D, there is a map of all these pairs into a real Hilbert space whose distances lie between the original distances and D times them if and only if min(sqrt(n),1/s)≤D.
-/

theorem ose_two_layer_cube_exact_hilbert_distortion (n : ℕ) (hn : 2 ≤ n) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hid : s ^ 2 + 2 * r * s = 1) (M : MetricSpace (Bool × (Fin n → Bool))) : letI := M; (∀ (x y : Fin n → Bool), dist (false,x) (false,y) = Real.sqrt (hammingDist x y : ℝ)) → (∀ (x y : Fin n → Bool), dist (false,x) (true,y) = Real.sqrt (r ^ 2 + (hammingDist x y : ℝ))) → (∀ (x y : Fin n → Bool), dist (true,x) (true,y) = min (s * (hammingDist x y : ℝ)) (Real.sqrt (hammingDist x y : ℝ))) → ∀ D : ℝ, EmbedsIntoHilbertWithDistortion (Bool × (Fin n → Bool)) D ↔ min (Real.sqrt (n : ℝ)) (1 / s) ≤ D := by
  intro hAA hAB hBB D
  let q : ℝ := Real.sqrt (n : ℝ)
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hqpos : 0 < q := Real.sqrt_pos.2 hnpos
  have hqn : q^2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hnpos)
  have hq2 : 2 ≤ q^2 := by rw [hqn]; exact_mod_cast hn
  have hs1 : s ≤ 1 := by nlinarith [mul_pos hr hs]
  let m : ℝ := min (s*(n : ℝ)) q
  have hm0 : 0 ≤ m := le_min (mul_nonneg hs.le (le_of_lt hnpos)) (le_of_lt hqpos)
  have hanti (x : Fin n → Bool) : dist (true,x) (true,fun i => !(x i)) = m := by
    rw [hBB, ose_hamming_antipode]
  have hedge (x : Fin n → Bool) (i : Fin n) :
      dist (true,x) (true,Function.update x i (!(x i))) = s := by
    rw [hBB, ose_hamming_flip]
    norm_num
    exact hs1
  constructor
  · intro hD
    rcases hD with ⟨H, hH, hI, hC, F, hF⟩
    letI : NormedAddCommGroup H := hH
    letI : InnerProductSpace ℝ H := hI
    letI : CompleteSpace H := hC
    have htype := ose_cube_hilbert_antipodal_inequality n H (fun x => F (true,x))
    have hbound := ose_cube_scale_distortion_lower n (by omega) M m s D hm0 hs H hanti hedge F hF htype
    have hsqpos : 0 < s*q := mul_pos hs hqpos
    have hminprod : min q (1/s) * (s*q) = m := by
      rw [min_mul_of_nonneg q (1/s) (le_of_lt hsqpos)]
      have e1 : q * (s*q) = s*(n : ℝ) := by rw [← hqn]; ring
      have e2 : (1/s) * (s*q) = q := by field_simp [ne_of_gt hs]
      rw [e1,e2]
    have hprod : min q (1/s) * (s*q) ≤ D * (s*q) := by
      rw [hminprod]
      nlinarith only [hbound]
    exact le_of_mul_le_mul_right hprod hsqpos
  · intro hD
    let U : (Fin n → Bool) → EuclideanSpace ℝ (Fin n) :=
      fun x => WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else 0)
    let c : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ)/2)
    have hU (x : Fin n → Bool) : ‖U x-c‖^2 = q^2/4 := by
      rw [hqn]
      exact (ose_boolean_cube_geometry n).1 x
    have hUsep (x y : Fin n → Bool) (hxy : x ≠ y) : 1 ≤ dist (U x) (U y) := by
      have h := (ose_boolean_cube_geometry n).2 x y hxy
      have hd : 0 ≤ dist (U x) (U y) := dist_nonneg
      nlinarith
    have hUsq (x y : Fin n → Bool) : dist (U x) (U y)^2 = (hammingDist x y : ℝ) :=
      ose_boolean_cube_dist_sq_hamming n x y
    have hUdist (x y : Fin n → Bool) : dist (U x) (U y) = Real.sqrt (hammingDist x y : ℝ) := by
      have h := hUsq x y
      have hr0 : 0 ≤ (hammingDist x y : ℝ) := by positivity
      have hroot := Real.sq_sqrt hr0
      have hd : 0 ≤ dist (U x) (U y) := dist_nonneg
      have hsqrt := Real.sqrt_nonneg (hammingDist x y : ℝ)
      nlinarith
    have hf (x y : Fin n → Bool) : dist (false,x) (false,y) = dist (U x) (U y) := by
      rw [hAA,hUdist]
    have hc (x y : Fin n → Bool) : dist (false,x) (true,y)^2 = r^2+dist (U x) (U y)^2 := by
      rw [hAB,Real.sq_sqrt (by positivity),hUsq]
    have hb (x y : Fin n → Bool) : dist (true,x) (true,y) =
        min (s*dist (U x) (U y)^2) (dist (U x) (U y)) := by
      rw [hBB,hUsq,hUdist]
    have hgood := ose_spherical_two_layer_hilbert_distortion_upper (Fin n → Bool)
      (EuclideanSpace ℝ (Fin n)) U c q r s hqpos hq2 hr hs hid hU hUsep M hf hc hb
    rcases hgood with ⟨H, hH, hI, hC, F, hF⟩
    letI : NormedAddCommGroup H := hH
    letI : InnerProductSpace ℝ H := hI
    letI : CompleteSpace H := hC
    refine ⟨H,hH,hI,hC,F,fun x y => ⟨(hF x y).1, ?_⟩⟩
    exact le_trans (hF x y).2 (mul_le_mul_of_nonneg_right hD dist_nonneg)
