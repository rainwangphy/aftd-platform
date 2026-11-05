import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# probabilistic_serial_fractional_assignment_two_split_swap

Topic: social_choice   Node: 3edac539717b

Provenance: helper lemma. lemma for probabilistic_serial_line_distortion_le_two_agents (OP-1158): the probabilistic serial assignment for two agents

Two agents whose first choices are item 1 (agent 0) and item 0 (agent 1) each get their first choice entirely under probabilistic serial.
-/

theorem probabilistic_serial_fractional_assignment_two_split_swap (pref : Fin 2 → Equiv.Perm (Fin 2)) (h0 : pref 0 0 = 1) (h1 : pref 1 0 = 0) (i j : Fin 2) :
    probabilistic_serial_fractional_assignment 2 pref i j = if j = i then 0 else 1 := by
  have e0 : (pref 0).symm 1 = 0 := by rw [Equiv.symm_apply_eq]; exact h0.symm
  have e1 : (pref 1).symm 0 = 0 := by rw [Equiv.symm_apply_eq]; exact h1.symm
  have f0 : (pref 0).symm 0 = 1 := by
    have : (pref 0).symm 0 ≠ 0 := fun h => by
      have := (pref 0).symm.injective (h.trans e0.symm); simp at this
    omega
  have f1 : (pref 1).symm 1 = 1 := by
    have : (pref 1).symm 1 ≠ 0 := fun h => by
      have := (pref 1).symm.injective (h.trans e1.symm); simp at this
    omega
  have he : ∀ i j : Fin 2, (0 < (fun _ => (1:ℝ)) j ∧ ∀ j', 0 < (fun _ : Fin 2 => (1:ℝ)) j' → (pref i).symm j ≤ (pref i).symm j') ↔ ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0)) := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [e0, e1, f0, f1]
  have hcard : ∀ x : Fin 2, ({x_1 : Fin 2 | x_1 = 0 ∧ x = 1 ∨ x_1 = 1 ∧ x = 0} : Finset (Fin 2)).card = 1 := by
    intro x; fin_cases x <;> decide
  have p1 : probabilistic_serial_phase 2 pref (fun _ => 1, fun _ _ => 0) =
      (fun _ => 0, fun i j => if j = i then 0 else 1) := by
    unfold probabilistic_serial_phase
    simp only [he, hcard]
    apply Prod.ext
    · funext j; fin_cases j <;> simp
    · funext i j; fin_cases i <;> fin_cases j <;> simp
  have p2 : probabilistic_serial_phase 2 pref (fun _ => 0, fun i j => if j = i then 0 else 1) =
      (fun _ => 0, fun i j => if j = i then 0 else 1) := by
    unfold probabilistic_serial_phase
    simp
  unfold probabilistic_serial_fractional_assignment
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, p1, p2]
