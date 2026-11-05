import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# probabilistic_serial_fractional_assignment_two_split

Topic: social_choice   Node: 70fa82db4e22

Provenance: helper lemma. lemma for probabilistic_serial_line_distortion_le_two_agents (OP-1158): the probabilistic serial assignment for two agents

Two agents whose first choices are item 0 (agent 0) and item 1 (agent 1) each get their first choice entirely under probabilistic serial.
-/

theorem probabilistic_serial_fractional_assignment_two_split (pref : Fin 2 → Equiv.Perm (Fin 2)) (h0 : pref 0 0 = 0) (h1 : pref 1 0 = 1) (i j : Fin 2) :
    probabilistic_serial_fractional_assignment 2 pref i j = if j = i then 1 else 0 := by
  have e0 : (pref 0).symm 0 = 0 := by rw [Equiv.symm_apply_eq]; exact h0.symm
  have e1 : (pref 1).symm 1 = 0 := by rw [Equiv.symm_apply_eq]; exact h1.symm
  have f0 : (pref 0).symm 1 = 1 := by
    have : (pref 0).symm 1 ≠ 0 := fun h => by
      have := (pref 0).symm.injective (h.trans e0.symm); simp at this
    omega
  have f1 : (pref 1).symm 0 = 1 := by
    have : (pref 1).symm 0 ≠ 0 := fun h => by
      have := (pref 1).symm.injective (h.trans e1.symm); simp at this
    omega
  have hr : ∀ i x : Fin 2, ((pref i).symm x ≤ (pref i).symm 0 ∧ (pref i).symm x ≤ (pref i).symm 1) ↔ x = i := by
    intro i x; fin_cases i <;> fin_cases x <;> simp [e0, e1, f0, f1]
  have hr0 : ∀ i : Fin 2, (pref i).symm 0 ≤ (pref i).symm 1 ↔ i = 0 := by
    intro i; fin_cases i <;> simp [e0, e1, f0, f1]
  have hr1 : ∀ i : Fin 2, (pref i).symm 1 ≤ (pref i).symm 0 ↔ i = 1 := by
    intro i; fin_cases i <;> simp [e0, e1, f0, f1]
  have p1 : probabilistic_serial_phase 2 pref (fun _ => 1, fun _ _ => 0) =
      (fun _ => 0, fun i j => if j = i then 1 else 0) := by
    unfold probabilistic_serial_phase
    ext a <;> fin_cases a <;> simp [Fin.forall_fin_two, hr, hr0, hr1, Finset.filter_eq', Finset.filter_eq] <;>
      (try (rename_i y; fin_cases y)) <;> try simp [e0, e1, f0, f1]
  have p2 : probabilistic_serial_phase 2 pref (fun _ => 0, fun i j => if j = i then 1 else 0) =
      (fun _ => 0, fun i j => if j = i then 1 else 0) := by
    unfold probabilistic_serial_phase
    simp
  unfold probabilistic_serial_fractional_assignment
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, p1, p2]
