import AFTD.Prelude
import AFTD.Kb.Tcs.OseBooleanCubeGeometry
import AFTD.Kb.Tcs.OseBooleanCubeEdgeExtensionLowerBound
import AFTD.Kb.Tcs.OneStronglyEuclideanSphericalCoreExtension
import AFTD.Kb.Tcs.OseBooleanCubeDistSqHamming
import AFTD.Kb.Tcs.OseHammingFlip

/-!
# ose_two_layer_cube_exact_extension_threshold

Topic: algorithms   Node: 0a34442b38c5

Provenance: original. Related work: arXiv:2611.08546, Sections 6.1–6.2, and one_strongly_euclidean_spherical_core_extension

Let n be a natural number at least one, and let r and s be positive real numbers with s²+2rs=1. Consider any metric on pairs (b,x), where b is a Boolean and x is a Boolean n-tuple, satisfying all three conditions: d((false,x),(false,y)) is the Euclidean distance between the 0-1 vectors x,y; d((false,x),(true,y))² is r² plus their squared Euclidean distance; and d((true,x),(true,x with coordinate i flipped))=s for every x and coordinate i. Then for every real D there exists a map F from all pairs into Euclidean n-space, equal to x on each (false,x) and satisfying dist(F(a),F(b))≤D*d(a,b) for all a,b, if and only if max(1,sqrt(n)/(2r+s*sqrt(n)))≤D.
-/

theorem ose_two_layer_cube_exact_extension_threshold (n : ℕ) (hn : 1 ≤ n) (r s : ℝ) (hr : 0 < r) (hs : 0 < s) (hid : s ^ 2 + 2 * r * s = 1) (M : MetricSpace (Bool × (Fin n → Bool))) : letI := M; (∀ (x y : Fin n → Bool), dist (false, x) (false, y) = dist (WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (fun i : Fin n => if y i then (1 : ℝ) else 0))) → (∀ (x y : Fin n → Bool), dist (false, x) (true, y) ^ 2 = r ^ 2 + dist (WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (fun i : Fin n => if y i then (1 : ℝ) else 0)) ^ 2) → (∀ (x : Fin n → Bool) (i : Fin n), dist (true, x) (true, Function.update x i (!(x i))) = s) → ∀ D : ℝ, (∃ F : (Bool × (Fin n → Bool)) → EuclideanSpace ℝ (Fin n), (∀ x, F (false, x) = WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0)) ∧ ∀ a b, dist (F a) (F b) ≤ D * dist a b) ↔ max 1 (Real.sqrt (n : ℝ) / (2 * r + s * Real.sqrt (n : ℝ))) ≤ D := by
  intro hf hc he D
  let U : (Fin n → Bool) → EuclideanSpace ℝ (Fin n) :=
    fun x => WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else 0)
  let c : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun _ => (1 : ℝ)/2)
  let q : ℝ := Real.sqrt (n : ℝ)
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hqn : q^2 = (n : ℝ) := Real.sq_sqrt hn0
  have hq1 : 1 ≤ q := Real.one_le_sqrt.mpr (by exact_mod_cast hn)
  have hU (x : Fin n → Bool) : ‖U x-c‖^2 = q^2/4 := by
    rw [hqn]
    exact (ose_boolean_cube_geometry n).1 x
  have hUsep (x y : Fin n → Bool) (hxy : x ≠ y) : 1 ≤ dist (U x) (U y)^2 :=
    (ose_boolean_cube_geometry n).2 x y hxy
  constructor
  · rintro ⟨F,hFixed,hLip⟩
    let x0 : Fin n → Bool := fun _ => false
    let i0 : Fin n := ⟨0, by omega⟩
    let y0 : Fin n → Bool := Function.update x0 i0 (!(x0 i0))
    have hUsq : dist (U x0) (U y0)^2 = 1 := by
      have h := ose_boolean_cube_dist_sq_hamming n x0 y0
      change dist (U x0) (U y0)^2 = (hammingDist x0 y0 : ℝ) at h
      have hham : hammingDist x0 y0 = 1 := by
        dsimp [y0]
        exact ose_hamming_flip n x0 i0
      rw [hham] at h
      simpa only [Nat.cast_one] using h
    have hUedge : dist (U x0) (U y0) = 1 := by
      have hd : 0 ≤ dist (U x0) (U y0) := dist_nonneg
      nlinarith
    have hD : 1 ≤ D := by
      have h := hLip (false,x0) (false,y0)
      rw [hFixed x0,hFixed y0,hf x0 y0,hUedge] at h
      nlinarith
    let v : (Fin n → Bool) → EuclideanSpace ℝ (Fin n) := fun x => F (true,x)
    have hnear (x : Fin n → Bool) : dist (v x) (U x) ≤ D*r := by
      have hx := hc x x
      simp only [dist_self,zero_pow,add_zero] at hx
      have hdist : dist (true,x) (false,x) = r := by
        rw [dist_comm]
        have hd : 0 ≤ dist (false,x) (true,x) := dist_nonneg
        nlinarith
      have h := hLip (true,x) (false,x)
      rw [hFixed x,hdist] at h
      exact h
    have hedge (x : Fin n → Bool) (i : Fin n) : dist (v x) (v (Function.update x i (!(x i)))) ≤ D*s := by
      have h := hLip (true,x) (true,Function.update x i (!(x i)))
      rw [he x i] at h
      exact h
    have hlower := ose_boolean_cube_edge_extension_lower_bound n r s D (by linarith) hr.le hs.le v hnear hedge
    have hden : 0 < 2*r+s*q := by positivity
    have hfrac : q/(2*r+s*q) ≤ D := (div_le_iff₀ hden).2 (by dsimp [q] at *; nlinarith [hlower])
    exact max_le hD hfrac
  · intro hD
    have hf' (x y : Fin n → Bool) : dist (false,x) (false,y) = dist (U x) (U y) := hf x y
    have hc' (x y : Fin n → Bool) : dist (false,x) (true,y)^2 = r^2+dist (U x) (U y)^2 := hc x y
    obtain ⟨F,hFixed,hLip⟩ := one_strongly_euclidean_spherical_core_extension (Fin n → Bool)
      (EuclideanSpace ℝ (Fin n)) U c q r s hq1 hr hs hid hU hUsep M hf' hc'
    refine ⟨F,hFixed,fun a b => ?_⟩
    exact le_trans (hLip a b) (mul_le_mul_of_nonneg_right hD dist_nonneg)
