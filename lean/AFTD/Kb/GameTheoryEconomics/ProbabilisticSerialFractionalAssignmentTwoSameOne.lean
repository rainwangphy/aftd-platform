import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# probabilistic_serial_fractional_assignment_two_same_one

Topic: social_choice   Node: 1dafb9ae44f2

Provenance: helper lemma. lemma for probabilistic_serial_line_distortion_le_two_agents (OP-1158): the probabilistic serial assignment for two agents

Two agents who both rank item 1 first each get half of each item under probabilistic serial.
-/

theorem probabilistic_serial_fractional_assignment_two_same_one (pref : Fin 2 → Equiv.Perm (Fin 2)) (h0 : pref 0 0 = 1) (h1 : pref 1 0 = 1) (i j : Fin 2) :
    probabilistic_serial_fractional_assignment 2 pref i j = 1 / 2 := by
  have e0 : (pref 0).symm 1 = 0 := by rw [Equiv.symm_apply_eq]; exact h0.symm
  have e1 : (pref 1).symm 1 = 0 := by rw [Equiv.symm_apply_eq]; exact h1.symm
  have f0 : (pref 0).symm 0 = 1 := by
    have : (pref 0).symm 0 ≠ 0 := fun h => by
      have := (pref 0).symm.injective (h.trans e0.symm); simp at this
    omega
  have f1 : (pref 1).symm 0 = 1 := by
    have : (pref 1).symm 0 ≠ 0 := fun h => by
      have := (pref 1).symm.injective (h.trans e1.symm); simp at this
    omega
  have hr : ∀ i x : Fin 2, ((pref i).symm x ≤ (pref i).symm 0 ∧ (pref i).symm x ≤ (pref i).symm 1) ↔ x = 1 := by
    intro i x; fin_cases i <;> fin_cases x <;> simp [e0, e1, f0, f1]
  have hS : (Finset.univ.filter fun x : Fin 2 =>
      (if x = 1 then (Finset.univ : Finset (Fin 2)) else ∅).Nonempty) = {1} := by
    ext x; fin_cases x <;> simp
  have p1 : probabilistic_serial_phase 2 pref (fun _ => 1, fun _ _ => 0) =
      (fun j => if j = 1 then 0 else 1, fun _ j => if j = 1 then 1 / 2 else 0) := by
    unfold probabilistic_serial_phase
    ext j <;> fin_cases j <;> simp [Fin.forall_fin_two, hr, Finset.filter_true_of_mem, hS, e0, e1, f0, f1] <;>
      (rename_i y; fin_cases y <;> simp [e0, e1, f0, f1])
  have hq : ∀ i x : Fin 2, ((0 < if x = 1 then (0:ℝ) else 1) ∧ (pref i).symm x ≤ (pref i).symm 0) ↔ x = 0 := by
    intro i x; fin_cases i <;> fin_cases x <;> simp [e0, e1, f0, f1]
  have hS2 : (Finset.univ.filter fun x : Fin 2 =>
      (if x = 0 then (Finset.univ : Finset (Fin 2)) else ∅).Nonempty) = {0} := by
    ext x; fin_cases x <;> simp
  have p2 : probabilistic_serial_phase 2 pref
      (fun j => if j = 1 then 0 else 1, fun _ j => if j = 1 then 1 / 2 else 0) =
      (fun _ => 0, fun _ _ => 1 / 2) := by
    unfold probabilistic_serial_phase
    ext a <;> fin_cases a <;> simp [Fin.forall_fin_two, hq, hS2, e0, e1, f0, f1] <;>
      (rename_i y; fin_cases y <;> simp [e0, e1, f0, f1])
  unfold probabilistic_serial_fractional_assignment
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, p1, p2]
