import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTriangleMatrix
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.ComparisonTriangleKappa
import AFTD.Kb.Tcs.ComparisonFeature2
import AFTD.Kb.Tcs.ComparisonTriangle
import AFTD.Kb.Tcs.ComparisonEdge
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# comparison_triangle_gram

Topic: quantum   Node: 77bf7f1d3fdc

Provenance: helper lemma. Step of arXiv:2610.34762 (Quantum ordinal selection with two comparisons), Section 3.1, Lemma 1 (quadratic_comparison_evaluation_kernel_and_projector)

The Gram matrix of the triangle relation vectors is U_triangle^T U_triangle = 3 I + 1 1^T: each kappa_abc has squared norm 4 and two distinct ones share only the constant coordinate, where both are -1.
-/

lemma comparison_triangle_gram_pair_eq_pair_iff_finset {α : Type*} [DecidableEq α] {x y z w : α} :
    ({x, y} : Finset α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z := by
  rw [← Finset.coe_inj]
  simp [Set.pair_eq_pair_iff]

lemma comparison_triangle_gram_same (n : ℕ) (t : comparison_triangle n) :
    ∑ j : comparison_feature2 n, comparison_triangle_kappa t j * comparison_triangle_kappa t j = 4 := by
  classical
  obtain ⟨⟨a, b, c⟩, hab, hbc⟩ := t
  dsimp at hab hbc
  dsimp [comparison_triangle_kappa]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, if_false, sub_zero, Subtype.ext_iff,
    comparison_triangle_gram_pair_eq_pair_iff_finset, Prod.ext_iff]
  have hab' : a ≠ b := ne_of_lt hab
  have hbc' : b ≠ c := ne_of_lt hbc
  simp [hab', hab'.symm, hbc', hbc'.symm]
  norm_num

lemma comparison_triangle_gram_diff (n : ℕ) (t1 t2 : comparison_triangle n) (hne : t1 ≠ t2) :
    ∑ j : comparison_feature2 n, comparison_triangle_kappa t1 j * comparison_triangle_kappa t2 j = 1 := by
  classical
  obtain ⟨⟨a1, b1, c1⟩, h1ab, h1bc⟩ := t1
  obtain ⟨⟨a2, b2, c2⟩, h2ab, h2bc⟩ := t2
  dsimp at h1ab h1bc h2ab h2bc
  have hne' : (a1, b1, c1) ≠ (a2, b2, c2) := fun h => hne (Subtype.ext h)
  dsimp [comparison_triangle_kappa]
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, if_false, sub_zero, Subtype.ext_iff,
    comparison_triangle_gram_pair_eq_pair_iff_finset, Prod.ext_iff]
  have h_cases :
    ¬ ((a2 = a1 ∧ b2 = b1) ∧ a2 = a1 ∧ c2 = c1 ∨ (a2 = a1 ∧ b2 = c1) ∧ a2 = a1 ∧ c2 = b1) ∧
    ¬ ((a2 = a1 ∧ b2 = b1) ∧ a2 = b1 ∧ c2 = c1 ∨ (a2 = b1 ∧ b2 = c1) ∧ a2 = a1 ∧ c2 = b1) ∧
    ¬ ((a2 = a1 ∧ b2 = c1) ∧ a2 = b1 ∧ c2 = c1 ∨ (a2 = b1 ∧ b2 = c1) ∧ a2 = a1 ∧ c2 = c1) ∧
    ¬ ((a2 = a1 ∧ b2 = b1) ∧ b2 = a1 ∧ c2 = c1 ∨ (a2 = a1 ∧ b2 = c1) ∧ b2 = a1 ∧ c2 = b1) ∧
    ¬ ((a2 = a1 ∧ b2 = b1) ∧ b2 = b1 ∧ c2 = c1 ∨ (a2 = b1 ∧ b2 = c1) ∧ b2 = a1 ∧ c2 = b1) ∧
    ¬ ((a2 = a1 ∧ b2 = c1) ∧ b2 = b1 ∧ c2 = c1 ∨ (a2 = b1 ∧ b2 = c1) ∧ b2 = a1 ∧ c2 = c1) ∧
    ¬ ((a2 = a1 ∧ c2 = b1) ∧ b2 = a1 ∧ c2 = c1 ∨ (a2 = a1 ∧ c2 = c1) ∧ b2 = a1 ∧ c2 = b1) ∧
    ¬ ((a2 = a1 ∧ c2 = b1) ∧ b2 = b1 ∧ c2 = c1 ∨ (a2 = b1 ∧ c2 = c1) ∧ b2 = a1 ∧ c2 = b1) ∧
    ¬ ((a2 = a1 ∧ c2 = c1) ∧ b2 = b1 ∧ c2 = c1 ∨ (a2 = b1 ∧ c2 = c1) ∧ b2 = a1 ∧ c2 = c1) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    { intro h
      rcases h with (⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ | ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩) <;>
      subst_vars <;>
      first | exact hne' rfl | exact (lt_asymm h1bc h2bc).elim | exact (lt_asymm h1ab h2ab).elim
            | omega }
  rcases h_cases with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9]

theorem comparison_triangle_gram (n : ℕ) :
    (comparison_triangle_matrix n).transpose * comparison_triangle_matrix n =
      (3 : ℝ) • (1 : Matrix (comparison_triangle n) (comparison_triangle n) ℝ) +
        Matrix.of (fun _ _ => (1 : ℝ)) := by
  ext t1 t2
  simp only [Matrix.mul_apply, Matrix.transpose_apply, comparison_triangle_matrix, Matrix.of_apply,
    Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply]
  by_cases h : t1 = t2
  · subst h
    rw [if_pos rfl, comparison_triangle_gram_same]
    norm_num
  · rw [if_neg h, comparison_triangle_gram_diff n t1 t2 h]
    norm_num
