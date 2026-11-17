import AFTD.Prelude

/-!
# op1525_class_imbalance_flip_bilinear_sum

Topic: combinatorics   Node: 45a560ad7bae

Provenance: helper lemma. The class-imbalance Gram-matrix reconstruction identity in the multipartite route for OP-1525.

For a finite set of vertices colored by signs and partitioned into classes, sum the product of the class-a and class-b sign imbalances after flipping each vertex once. The result is (n−4) times the original product, plus four times the size of class a if a=b.
-/

theorem op1525_class_imbalance_flip_bilinear_sum
    {V J : Type*} [DecidableEq J] [Fintype V]
    (cl : V → J) (f : V → ℤ) (hsgn : ∀ v, f v = 1 ∨ f v = -1)
    (a b : J) :
    let D : J → ℤ := fun j => ∑ u : V, if cl u = j then f u else 0
    (∑ v : V, (D a - 2 * (if cl v = a then f v else 0)) *
      (D b - 2 * (if cl v = b then f v else 0))) =
      ((Fintype.card V : ℤ) - 4) * D a * D b +
        if a = b then 4 * (((Finset.univ : Finset V).filter (fun v => cl v = a)).card : ℤ) else 0 := by
  classical
  dsimp only
  let D : J → ℤ := fun j => ∑ u : V, if cl u = j then f u else 0
  change (∑ v : V, (D a - 2 * (if cl v = a then f v else 0)) *
      (D b - 2 * (if cl v = b then f v else 0))) = _
  have hs (v : V) : f v * f v = 1 := by
    rcases hsgn v with h | h <;> rw [h] <;> norm_num
  have hcross : (∑ v : V, (if cl v = a then f v else 0) *
        (if cl v = b then f v else 0)) =
      if a = b then (((Finset.univ : Finset V).filter (fun v => cl v = a)).card : ℤ) else 0 := by
    by_cases hab : a = b
    · subst b
      simp only [if_true]
      have heq (v : V) : (if cl v = a then f v else 0) *
          (if cl v = a then f v else 0) = if cl v = a then 1 else 0 := by
        split_ifs <;> simp_all
      simp only [heq]
      simp
    · simp only [hab, if_false]
      apply Finset.sum_eq_zero
      intro v _
      split_ifs with ha hb <;> simp_all
  have hterm (v : V) : (D a - 2 * (if cl v = a then f v else 0)) *
      (D b - 2 * (if cl v = b then f v else 0)) =
      D a * D b - 2 * D b * (if cl v = a then f v else 0) -
      2 * D a * (if cl v = b then f v else 0) +
      4 * ((if cl v = a then f v else 0) * (if cl v = b then f v else 0)) := by ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  change D a * ((Fintype.card V : ℤ) * D b) - 2 * D b * D a -
    2 * D a * D b + 4 * (∑ v : V, (if cl v = a then f v else 0) *
        (if cl v = b then f v else 0)) = _
  rw [hcross]
  split_ifs <;> ring
