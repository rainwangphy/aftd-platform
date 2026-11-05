import AFTD.Prelude
import AFTD.Kb.Tcs.MordellTenExistsFeasibleGtChalk

/-!
# mordell_ten_suboptimal

Topic: combinatorics   Node: ece6a008311f

Provenance: formalization of a published result. Source: arXiv:2611.03088 Proposition 5.1

In Mordell's problem for ten points in the complex plane, the supremum sSup of { d : ℝ | ∃ z : Fin 10 → ℂ, (∑ i : Fin 10, ‖z i‖^2 = 10) ∧ d = ∏ i : Fin 10, ∏ j : Fin 10 with i < j, ‖z i - z j‖^2 } strictly exceeds (10 : ℝ)^45 / (9 : ℝ)^36.
-/

lemma mordell_ten_suboptimal_bddAbove :
    BddAbove { d : ℝ | ∃ z : Fin 10 → ℂ, (∑ i : Fin 10, ‖z i‖ ^ 2 = 10) ∧
      d = ∏ i : Fin 10, ∏ j : Fin 10 with i < j, ‖z i - z j‖ ^ 2 } := by
  use ∏ i : Fin 10, ∏ j : Fin 10 with i < j, (40 : ℝ)
  rintro d ⟨z, hz, rfl⟩
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.prod_nonneg fun _ _ => sq_nonneg _
  · intro i _
    apply Finset.prod_le_prod
    · intro j _
      exact sq_nonneg _
    · intro j _
      have h1 : ‖z i - z j‖ ≤ ‖z i‖ + ‖z j‖ := norm_sub_le (z i) (z j)
      have h2 : ‖z i - z j‖ ^ 2 ≤ (‖z i‖ + ‖z j‖) ^ 2 := by
        nlinarith [norm_nonneg (z i - z j), norm_nonneg (z i), norm_nonneg (z j)]
      have h3 : 2 * (‖z i‖ ^ 2 + ‖z j‖ ^ 2) - (‖z i‖ + ‖z j‖) ^ 2 = (‖z i‖ - ‖z j‖) ^ 2 := by ring
      have h4 : (‖z i‖ - ‖z j‖) ^ 2 ≥ 0 := sq_nonneg _
      have h_zi : ‖z i‖ ^ 2 ≤ 10 := by
        have := Finset.single_le_sum (fun (k : Fin 10) _ => sq_nonneg (‖z k‖)) (Finset.mem_univ i)
        linarith
      have h_zj : ‖z j‖ ^ 2 ≤ 10 := by
        have := Finset.single_le_sum (fun (k : Fin 10) _ => sq_nonneg (‖z k‖)) (Finset.mem_univ j)
        linarith
      linarith

/-- Suboptimality of the centered regular polygon configuration for ten points in Mordell's problem. -/
theorem mordell_ten_suboptimal :
    sSup { d : ℝ | ∃ z : Fin 10 → ℂ, (∑ i : Fin 10, ‖z i‖ ^ 2 = 10) ∧
      d = ∏ i : Fin 10, ∏ j : Fin 10 with i < j, ‖z i - z j‖ ^ 2 } >
    (10 : ℝ) ^ 45 / (9 : ℝ) ^ 36 := by
  obtain ⟨z, hz_sum, hz_gt⟩ := mordell_ten_exists_feasible_gt_chalk
  let S := { d : ℝ | ∃ z : Fin 10 → ℂ, (∑ i : Fin 10, ‖z i‖ ^ 2 = 10) ∧
    d = ∏ i : Fin 10, ∏ j : Fin 10 with i < j, ‖z i - z j‖ ^ 2 }
  have hmem : (∏ i : Fin 10, ∏ j : Fin 10 with i < j, ‖z i - z j‖ ^ 2) ∈ S :=
    ⟨z, hz_sum, rfl⟩
  exact lt_csSup_of_lt mordell_ten_suboptimal_bddAbove hmem hz_gt
