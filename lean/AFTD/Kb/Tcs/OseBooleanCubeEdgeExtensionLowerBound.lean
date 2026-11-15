import AFTD.Prelude
import AFTD.Kb.Tcs.OseCubeUniformAntipodalBound
import AFTD.Kb.Tcs.OseBooleanCubeDistSqHamming
import AFTD.Kb.Tcs.OseHammingAntipode

/-!
# ose_boolean_cube_edge_extension_lower_bound

Topic: algorithms   Node: 7682aa88308d

Provenance: helper lemma. arXiv:2611.08546, Section 6.2, lower-bound argument

For an arbitrary placement of images of the Boolean cube vertices in Euclidean n-space, if every image lies within Lr of its corresponding cube vertex and every cube edge has image length at most Ls, then sqrt(n) is at most L times (2r+s sqrt(n)).
-/

theorem ose_boolean_cube_edge_extension_lower_bound (n : ℕ) (r s L : ℝ) (hL : 0 ≤ L) (hr : 0 ≤ r) (hs : 0 ≤ s) (v : (Fin n → Bool) → EuclideanSpace ℝ (Fin n)) (hnear : ∀ x, dist (v x) (WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0) : EuclideanSpace ℝ (Fin n)) ≤ L * r) (hedge : ∀ x i, dist (v x) (v (Function.update x i (!(x i)))) ≤ L * s) : Real.sqrt (n : ℝ) ≤ L * (2 * r + s * Real.sqrt (n : ℝ)) := by
  let q : ℝ := Real.sqrt (n : ℝ)
  let t : ℝ := max 0 (q-2*L*r)
  let U : (Fin n → Bool) → EuclideanSpace ℝ (Fin n) :=
    fun x => WithLp.toLp 2 (fun i => if x i then (1 : ℝ) else 0)
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have ht0 : 0 ≤ t := le_max_left _ _
  have hantiU (x : Fin n → Bool) : dist (U x) (U (fun i => !(x i))) = q := by
    have h := ose_boolean_cube_dist_sq_hamming n x (fun i => !(x i))
    rw [ose_hamming_antipode] at h
    change dist (U x) (U (fun i => !(x i)))^2 = (n : ℝ) at h
    have hq : q^2 = (n : ℝ) := Real.sq_sqrt (by positivity)
    have hd : 0 ≤ dist (U x) (U (fun i => !(x i))) := dist_nonneg
    nlinarith
  have hlow (x : Fin n → Bool) : t ≤ dist (v x) (v (fun i => !(x i))) := by
    apply max_le
    · exact dist_nonneg
    · have h1 := dist_triangle (U x) (v x) (U (fun i => !(x i)))
      have h2 := dist_triangle (v x) (v (fun i => !(x i))) (U (fun i => !(x i)))
      have hn1 := hnear x
      have hn2 := hnear (fun i => !(x i))
      rw [dist_comm (U x) (v x)] at h1
      rw [hantiU] at h1
      nlinarith [h1,h2,hn1,hn2]
  have hbound := ose_cube_uniform_antipodal_bound n (EuclideanSpace ℝ (Fin n)) v t (L*s)
    ht0 (mul_nonneg hL hs) hlow hedge
  have ht := le_max_right (0 : ℝ) (q-2*L*r)
  dsimp [t] at hbound
  dsimp [q] at *
  nlinarith only [hbound,ht]
