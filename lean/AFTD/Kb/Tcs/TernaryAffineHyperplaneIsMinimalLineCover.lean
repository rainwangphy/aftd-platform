import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimalTernaryLineCover
import AFTD.Kb.Tcs.TernaryAffineHyperplane
import AFTD.Kb.Tcs.IsTernaryLineCover

/-!
# ternary_affine_hyperplane_is_minimal_line_cover

Topic: combinatorics   Node: d0d1b87a6e16

Provenance: formalization of a published result. Source: arXiv:2610.32789, Section 3.1

For any integer $n \ge 1$, any vector $a : \mathrm{Fin}\ n \to \mathbb{Z}/3\mathbb{Z}$ with all coordinates nonzero, and any scalar $b \in \mathbb{Z}/3\mathbb{Z}$, the affine hyperplane $\{x \in (\mathbb{Z}/3\mathbb{Z})^n \mid \sum_{i} a(i) x(i) = b\}$ is an inclusion-minimal ternary line cover of $(\mathbb{Z}/3\mathbb{Z})^n$.
-/

private lemma ternary_affine_hyperplane_is_minimal_line_cover_sum_mul_update
    (n : ℕ) (a c : Fin n → ZMod 3) (i : Fin n) (t : ZMod 3) :
    (∑ j : Fin n, a j * (Function.update c i t) j)
      = (∑ j ∈ Finset.univ.erase i, a j * c j) + a i * t := by
  rw [← Finset.sum_erase_add (s := Finset.univ)
        (f := fun j => a j * (Function.update c i t) j) (a := i) (Finset.mem_univ i)]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    rw [Function.update_apply]
    simp [hji]
  · rw [Function.update_apply]
    simp

/-- Every affine hyperplane with nonzero normal coefficients is an inclusion-minimal line cover. -/
theorem ternary_affine_hyperplane_is_minimal_line_cover (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ZMod 3) (ha : ∀ i, a i ≠ 0) (b : ZMod 3) : is_minimal_ternary_line_cover n (ternary_affine_hyperplane n a b) := by
  unfold is_minimal_ternary_line_cover
  refine ⟨?_, ?_⟩
  · intro i c
    refine ⟨(a i)⁻¹ * (b - ∑ j ∈ Finset.univ.erase i, a j * c j), ?_⟩
    simp only [ternary_affine_hyperplane, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ternary_affine_hyperplane_is_minimal_line_cover_sum_mul_update]
    rw [← mul_assoc, mul_inv_cancel₀ (ha i), one_mul]
    ring
  · intro B' hB' hcover
    apply Finset.Subset.antisymm hB'
    intro x hx
    let i : Fin n := ⟨0, hn⟩
    obtain ⟨t, ht⟩ := hcover i x
    have htH : Function.update x i t ∈ ternary_affine_hyperplane n a b := hB' ht
    simp only [ternary_affine_hyperplane, Finset.mem_filter, Finset.mem_univ, true_and] at hx htH
    have hti : t = x i := by
      have h1 : ∑ j : Fin n, a j * (Function.update x i t) j = ∑ j : Fin n, a j * x j := by
        rw [htH, hx]
      rw [ternary_affine_hyperplane_is_minimal_line_cover_sum_mul_update,
        ← Finset.sum_erase_add (s := Finset.univ) (f := fun j => a j * x j) (a := i) (Finset.mem_univ i)] at h1
      exact mul_left_cancel₀ (ha i) (add_left_cancel h1)
    have hux : Function.update x i t = x := by
      funext j
      rw [Function.update_apply]
      by_cases hji : j = i
      · simp [hji, hti]
      · simp [hji]
    rw [← hux]
    exact ht
