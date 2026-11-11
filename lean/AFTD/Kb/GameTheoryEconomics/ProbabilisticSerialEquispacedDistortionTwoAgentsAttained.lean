import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCostLe
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignmentTwoSame

/-!
# probabilistic_serial_equispaced_distortion_two_agents_attained

Topic: social_choice   Node: 3a950dcb8fd3

Provenance: original. Related work: OP-1441

For n = 2 with equispaced items at 0 and 1, agents at 0 and 1/2 with ties broken toward the smaller-index item attain the harmonic distortion bound of 2 exactly.
-/

/-- Sharpness of OP-1441 for n = 2: the harmonic distortion bound is attained by agents at 0 and 1/2. -/
theorem probabilistic_serial_equispaced_distortion_two_agents_attained :
    ∃ pref : Fin 2 → Equiv.Perm (Fin 2),
      (∀ (i k k' : Fin 2), k < k' →
        |((if i.val < 2 - 1 then (i : ℝ) else (2 : ℝ) - 3 / 2) - ((pref i k : Fin 2) : ℝ))| <
          |((if i.val < 2 - 1 then (i : ℝ) else (2 : ℝ) - 3 / 2) - ((pref i k' : Fin 2) : ℝ))| ∨
        (|((if i.val < 2 - 1 then (i : ℝ) else (2 : ℝ) - 3 / 2) - ((pref i k : Fin 2) : ℝ))| =
          |((if i.val < 2 - 1 then (i : ℝ) else (2 : ℝ) - 3 / 2) - ((pref i k' : Fin 2) : ℝ))| ∧
          pref i k < pref i k')) ∧
      probabilistic_serial_line_cost
        (fun (i : Fin 2) => if i.val < 2 - 1 then (i : ℝ) else (2 : ℝ) - 3 / 2)
        (fun (j : Fin 2) => (j : ℝ)) pref =
        (1 + (harmonic (2 / 2) : ℝ) + (harmonic ((2 - 1) / 2) : ℝ)) *
          line_min_matching_cost
            (fun (i : Fin 2) => if i.val < 2 - 1 then (i : ℝ) else (2 : ℝ) - 3 / 2)
            (fun (j : Fin 2) => (j : ℝ)) := by
  use fun _ => 1
  constructor
  · intro i k k' h
    have : k = 0 ∧ k' = 1 := by
      fin_cases k <;> fin_cases k' <;> try omega
    rcases this with ⟨rfl, rfl⟩
    fin_cases i
    · left
      simp only [Equiv.Perm.coe_one, id]
      norm_num
    · right
      simp only [Equiv.Perm.coe_one, id]
      norm_num
  · have h_harm_0 : harmonic 0 = 0 := harmonic_zero
    have h_harm_1 : harmonic 1 = 1 := by
      change harmonic (0 + 1) = 1
      rw [harmonic_succ, harmonic_zero]
      simp
    have h_coef : (1 + (harmonic (2 / 2) : ℝ) + (harmonic ((2 - 1) / 2) : ℝ)) = 2 := by
      have h1 : 2 / 2 = 1 := rfl
      have h0 : (2 - 1) / 2 = 0 := rfl
      rw [h1, h0, h_harm_0, h_harm_1]
      push_cast
      ring
    have h_ps : probabilistic_serial_line_cost
        (fun (i : Fin 2) => if i.val < 2 - 1 then (i : ℝ) else (2 : ℝ) - 3 / 2)
        (fun (j : Fin 2) => (j : ℝ)) (fun _ => 1) = 1 := by
      unfold probabilistic_serial_line_cost
      simp only [Fin.sum_univ_two]
      simp only [probabilistic_serial_fractional_assignment_two_same (fun _ => 1) rfl rfl]
      norm_num
    have h_opt : line_min_matching_cost
        (fun (i : Fin 2) => if i.val < 2 - 1 then (i : ℝ) else (2 : ℝ) - 3 / 2)
        (fun (j : Fin 2) => (j : ℝ)) = 1 / 2 := by
      apply le_antisymm
      · have h := line_min_matching_cost_le
          (fun (i : Fin 2) => if i.val < 2 - 1 then (i : ℝ) else (2 : ℝ) - 3 / 2)
          (fun (j : Fin 2) => (j : ℝ)) 1
        simp only [Fin.sum_univ_two, Equiv.Perm.coe_one, id] at h
        norm_num at h ⊢
        exact h
      · unfold line_min_matching_cost
        apply Finset.le_inf'
        intro σ _
        have hp : ∀ π : Equiv.Perm (Fin 2), π = 1 ∨ π = Equiv.swap 0 1 := by decide
        rcases hp σ with rfl | rfl
        · simp only [Fin.sum_univ_two, Equiv.Perm.coe_one, id]
          norm_num
        · simp only [Fin.sum_univ_two, Equiv.swap_apply_left, Equiv.swap_apply_right]
          norm_num
    rw [h_coef, h_ps, h_opt]
    norm_num
