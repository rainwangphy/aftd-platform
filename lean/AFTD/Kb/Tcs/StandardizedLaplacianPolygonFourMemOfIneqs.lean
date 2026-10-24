import AFTD.Prelude
import AFTD.Kb.Tcs.StandardizedLaplacianPolygonFour

/-!
# standardized_laplacian_polygon_four_mem_of_ineqs

Topic: graphs   Node: 31d5735f2caa

Provenance: helper lemma. step towards standardized_laplacian_order_four_polygon_conjecture

Any complex number z satisfying |Im(z)| ≤ 1/4, |Im(z)| ≤ Re(z), and Re(z) + |Im(z)| ≤ 1 belongs to the standardized Laplacian polygon S_4.
-/

open Complex

abbrev standardized_laplacian_polygon_four_mem_of_ineqs_gen : Set ℂ :=
  { (1 / (4 : ℂ)) * ∑ m ∈ Finset.range (k + 1), (1 - (-Complex.I) ^ m) | k : Fin 4 } ∪
  { star ((1 / (4 : ℂ)) * ∑ m ∈ Finset.range (k + 1), (1 - (-Complex.I) ^ m)) | k : Fin 4 }

lemma standardized_laplacian_polygon_four_mem_of_ineqs_combo_three
    (p0 p1 p2 : ℂ)
    (hp0 : p0 ∈ standardized_laplacian_polygon_four_mem_of_ineqs_gen)
    (hp1 : p1 ∈ standardized_laplacian_polygon_four_mem_of_ineqs_gen)
    (hp2 : p2 ∈ standardized_laplacian_polygon_four_mem_of_ineqs_gen)
    (w0 w1 w2 : ℝ)
    (hw0 : 0 ≤ w0) (hw1 : 0 ≤ w1) (hw2 : 0 ≤ w2)
    (hsum : w0 + w1 + w2 = 1)
    {z : ℂ} (hz : z = w0 • p0 + w1 • p1 + w2 • p2) :
    z ∈ standardized_laplacian_polygon_four := by
  change z ∈ convexHull ℝ standardized_laplacian_polygon_four_mem_of_ineqs_gen
  rw [hz]
  refine mem_convexHull_of_exists_fintype (s := standardized_laplacian_polygon_four_mem_of_ineqs_gen)
    (x := w0 • p0 + w1 • p1 + w2 • p2)
    ![w0, w1, w2] ![p0, p1, p2] ?_ ?_ ?_ ?_
  · intro i; fin_cases i <;> simp [hw0, hw1, hw2]
  · simp [Fin.sum_univ_three, hsum]
  · intro i; fin_cases i <;> simp [hp0, hp1, hp2]
  · simp [Fin.sum_univ_three]

lemma standardized_laplacian_polygon_four_mem_of_ineqs_p0 :
    (0 : ℂ) ∈ standardized_laplacian_polygon_four_mem_of_ineqs_gen := by
  left; use ⟨0, by decide⟩; simp

lemma standardized_laplacian_polygon_four_mem_of_ineqs_p1 :
    (1/4 : ℂ) + Complex.I / 4 ∈ standardized_laplacian_polygon_four_mem_of_ineqs_gen := by
  left; use ⟨1, by decide⟩; simp [Finset.sum_range_succ]; ring

lemma standardized_laplacian_polygon_four_mem_of_ineqs_p2 :
    (3/4 : ℂ) + Complex.I / 4 ∈ standardized_laplacian_polygon_four_mem_of_ineqs_gen := by
  left; use ⟨2, by decide⟩; simp [Finset.sum_range_succ]; ring

lemma standardized_laplacian_polygon_four_mem_of_ineqs_p3 :
    (1 : ℂ) ∈ standardized_laplacian_polygon_four_mem_of_ineqs_gen := by
  left; use ⟨3, by decide⟩
  simp [Finset.sum_range_succ]
  have : (-Complex.I) ^ 3 = -(-Complex.I) := by
    calc (-Complex.I) ^ 3 = (-Complex.I) ^ 2 * (-Complex.I) := by ring
    _ = (Complex.I ^ 2) * (-Complex.I) := by ring
    _ = -1 * (-Complex.I) := by rw [Complex.I_sq]
    _ = -(-Complex.I) := by ring
  rw [this]; ring

lemma standardized_laplacian_polygon_four_mem_of_ineqs_p4 :
    (3/4 : ℂ) - Complex.I / 4 ∈ standardized_laplacian_polygon_four_mem_of_ineqs_gen := by
  right; use ⟨2, by decide⟩
  have h : (1 / (4 : ℂ)) * ∑ m ∈ Finset.range (2 + 1), (1 - (-Complex.I) ^ m) = 3/4 + Complex.I/4 := by
    simp [Finset.sum_range_succ]; ring
  rw [h]; simp; ring

lemma standardized_laplacian_polygon_four_mem_of_ineqs_p5 :
    (1/4 : ℂ) - Complex.I / 4 ∈ standardized_laplacian_polygon_four_mem_of_ineqs_gen := by
  right; use ⟨1, by decide⟩
  have h : (1 / (4 : ℂ)) * ∑ m ∈ Finset.range (1 + 1), (1 - (-Complex.I) ^ m) = 1/4 + Complex.I/4 := by
    simp [Finset.sum_range_succ]; ring
  rw [h]; simp; ring

/-- Any complex number z satisfying |Im(z)| ≤ 1/4, |Im(z)| ≤ Re(z), and Re(z) + |Im(z)| ≤ 1 belongs to the standardized Laplacian polygon S_4. -/
theorem standardized_laplacian_polygon_four_mem_of_ineqs (z : ℂ)
    (h_im_le : |z.im| ≤ (1 : ℝ) / 4)
    (h_left : |z.im| ≤ z.re)
    (h_right : z.re + |z.im| ≤ 1) :
    z ∈ standardized_laplacian_polygon_four := by
  by_cases h_im : 0 ≤ z.im
  · have h_abs : |z.im| = z.im := abs_of_nonneg h_im
    rw [h_abs] at h_im_le h_left h_right
    by_cases h_split : z.re + 3 * z.im ≤ 1
    · refine standardized_laplacian_polygon_four_mem_of_ineqs_combo_three
        0 ((1/4 : ℂ) + Complex.I / 4) 1
        standardized_laplacian_polygon_four_mem_of_ineqs_p0
        standardized_laplacian_polygon_four_mem_of_ineqs_p1
        standardized_laplacian_polygon_four_mem_of_ineqs_p3
        (1 - z.re - 3 * z.im) (4 * z.im) (z.re - z.im)
        (by linarith) (by linarith) (by linarith) (by ring) ?_
      apply Complex.ext <;> (simp; ring)
    · refine standardized_laplacian_polygon_four_mem_of_ineqs_combo_three
        ((1/4 : ℂ) + Complex.I / 4) ((3/4 : ℂ) + Complex.I / 4) 1
        standardized_laplacian_polygon_four_mem_of_ineqs_p1
        standardized_laplacian_polygon_four_mem_of_ineqs_p2
        standardized_laplacian_polygon_four_mem_of_ineqs_p3
        (2 * (1 - z.re - z.im)) (2 * (z.re + 3 * z.im - 1)) (1 - 4 * z.im)
        (by linarith) (by linarith) (by linarith) (by ring) ?_
      apply Complex.ext <;> (simp; ring)
  · have h_im_neg : z.im < 0 := by linarith
    have h_abs : |z.im| = -z.im := abs_of_neg h_im_neg
    rw [h_abs] at h_im_le h_left h_right
    by_cases h_split : z.re - 3 * z.im ≤ 1
    · refine standardized_laplacian_polygon_four_mem_of_ineqs_combo_three
        0 ((1/4 : ℂ) - Complex.I / 4) 1
        standardized_laplacian_polygon_four_mem_of_ineqs_p0
        standardized_laplacian_polygon_four_mem_of_ineqs_p5
        standardized_laplacian_polygon_four_mem_of_ineqs_p3
        (1 - z.re + 3 * z.im) (-4 * z.im) (z.re + z.im)
        (by linarith) (by linarith) (by linarith) (by ring) ?_
      apply Complex.ext <;> (simp; ring)
    · refine standardized_laplacian_polygon_four_mem_of_ineqs_combo_three
        ((1/4 : ℂ) - Complex.I / 4) ((3/4 : ℂ) - Complex.I / 4) 1
        standardized_laplacian_polygon_four_mem_of_ineqs_p5
        standardized_laplacian_polygon_four_mem_of_ineqs_p4
        standardized_laplacian_polygon_four_mem_of_ineqs_p3
        (2 * (1 - z.re + z.im)) (2 * (z.re - 3 * z.im - 1)) (1 + 4 * z.im)
        (by linarith) (by linarith) (by linarith) (by ring) ?_
      apply Complex.ext <;> (simp; ring)
