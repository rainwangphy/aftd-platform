import AFTD.Prelude

/-!
# ose_boolean_cube_dist_sq_hamming

Topic: algorithms   Node: 2a1e5581b2af

Provenance: helper lemma. arXiv:2611.08546, Section 6.1, Boolean-cube geometry

The squared Euclidean distance between two standard Boolean-cube vertices equals their Hamming distance.
-/

theorem ose_boolean_cube_dist_sq_hamming (n : ℕ) (x y : Fin n → Bool) : dist (WithLp.toLp 2 (fun i : Fin n => if x i then (1 : ℝ) else 0) : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 (fun i : Fin n => if y i then (1 : ℝ) else 0)) ^ 2 = (hammingDist x y : ℝ) := by
  classical
  rw [EuclideanSpace.dist_sq_eq]
  simp only [WithLp.ofLp_toLp]
  simp only [hammingDist, Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  cases hx : x i <;> cases hy : y i <;> norm_num [hx,hy,Real.dist_eq]
