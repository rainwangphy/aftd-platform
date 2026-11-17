import AFTD.Prelude
import AFTD.Kb.Tcs.ContinuousOddThreeSphereComplexZero

/-!
# three_qubit_odd_spinor_overlap_zero

Topic: quantum   Node: 477caa3ee1fd

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, the odd-overlap step; the existence of the required Bloch spinor lifts is a separate result.

If each component of three complex two-component spinors varies continuously and oddly on the unit three-sphere, then their tensor product has zero overlap with any prescribed three-qubit coefficient array for some point of that sphere.
-/

theorem three_qubit_odd_spinor_overlap_zero
    (ψ : (Fin 3 → Fin 2) → ℂ)
    (v : Fin 3 → (Fin 4 → ℝ) → Fin 2 → ℂ)
    (hcont : ∀ i j, ContinuousOn (fun q => v i q j) {q | (∑ k, (q k)^2) = 1})
    (hodd : ∀ i q, (∑ k, (q k)^2) = 1 → ∀ j, v i (-q) j = -v i q j) :
    ∃ q : Fin 4 → ℝ, (∑ k, (q k)^2) = 1 ∧
      (∑ s : Fin 3 → Fin 2, star (∏ i, v i q (s i)) * ψ s) = 0 := by
  let S : Set (Fin 4 → ℝ) := {q | (∑ k, (q k)^2) = 1}
  let F : (Fin 4 → ℝ) → ℂ := fun q =>
    ∑ s : Fin 3 → Fin 2, star (∏ i, v i q (s i)) * ψ s
  have hf : ContinuousOn F S := by
    dsimp [F]
    apply continuousOn_finsetSum
    intro s hs
    apply ContinuousOn.mul
    · apply ContinuousOn.star
      apply continuousOn_finsetProd
      intro i hi
      exact hcont i (s i)
    · exact continuousOn_const
  have ho : ∀ q, (∑ k, (q k)^2) = 1 → F (-q) = -F q := by
    intro q hq
    dsimp [F]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [Fin.prod_univ_three, hodd 0 q hq, hodd 1 q hq, hodd 2 q hq]
    have hp : (-v 0 q (s 0)) * (-v 1 q (s 1)) * (-v 2 q (s 2)) =
        -(v 0 q (s 0) * v 1 q (s 1) * v 2 q (s 2)) := by ring
    rw [hp]
    simp
  exact continuous_odd_three_sphere_complex_zero F hf ho
