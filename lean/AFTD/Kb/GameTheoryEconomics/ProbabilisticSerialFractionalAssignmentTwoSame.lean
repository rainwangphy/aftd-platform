import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# probabilistic_serial_fractional_assignment_two_same

Topic: social_choice   Node: 53e2b4976eff

Provenance: helper lemma. sanity lemma for probabilistic_serial_fractional_assignment (OP-1158)

Sanity check: when both of two agents rank item 0 first, probabilistic serial gives each agent half of each item.
-/

theorem probabilistic_serial_fractional_assignment_two_same
    (pref : Fin 2 → Equiv.Perm (Fin 2)) (h0 : pref 0 0 = 0) (h1 : pref 1 0 = 0) (i j : Fin 2) :
    probabilistic_serial_fractional_assignment 2 pref i j = 1 / 2 := by
  have e0 : (pref 0).symm 0 = 0 := by rw [Equiv.symm_apply_eq]; exact h0.symm
  have e1 : (pref 1).symm 0 = 0 := by rw [Equiv.symm_apply_eq]; exact h1.symm
  have f0 : (pref 0).symm 1 = 1 := by
    have : (pref 0).symm 1 ≠ 0 := fun h => by
      have := (pref 0).symm.injective (h.trans e0.symm); simp at this
    omega
  have f1 : (pref 1).symm 1 = 1 := by
    have : (pref 1).symm 1 ≠ 0 := fun h => by
      have := (pref 1).symm.injective (h.trans e1.symm); simp at this
    omega
  have hr : ∀ i x : Fin 2, ((pref i).symm x ≤ (pref i).symm 0 ∧ (pref i).symm x ≤ (pref i).symm 1) ↔ x = 0 := by
    intro i x; fin_cases i <;> fin_cases x <;> simp [e0, e1, f0, f1]
  have hr2 : ∀ i x : Fin 2, ((pref i).symm x = 0 ∧ (pref i).symm x ≤ 1) ↔ x = 0 := by
    intro i x; fin_cases i <;> fin_cases x <;> simp [e0, e1, f0, f1]
  have hS : (Finset.univ.filter fun x : Fin 2 =>
      (if x = 0 then (Finset.univ : Finset (Fin 2)) else ∅).Nonempty) = {0} := by
    ext x; fin_cases x <;> simp
  have p1 : probabilistic_serial_phase 2 pref (fun _ => 1, fun _ _ => 0) =
      (fun j => if j = 0 then 0 else 1, fun _ j => if j = 0 then 1 / 2 else 0) := by
    unfold probabilistic_serial_phase
    ext j <;> fin_cases j <;> simp [Fin.forall_fin_two, hr, hr2, Finset.filter_true_of_mem, hS, e0, e1, f0, f1]
  have hq : ∀ i x : Fin 2, ((0 < if x = 0 then (0:ℝ) else 1) ∧ (pref i).symm x ≤ (pref i).symm 1) ↔ x = 1 := by
    intro i x; fin_cases i <;> fin_cases x <;> simp [e0, e1, f0, f1]
  have hS2 : (Finset.univ.filter fun x : Fin 2 =>
      (if x = 1 then (Finset.univ : Finset (Fin 2)) else ∅).Nonempty) = {1} := by
    ext x; fin_cases x <;> simp
  have p2 : probabilistic_serial_phase 2 pref
      (fun j => if j = 0 then 0 else 1, fun _ j => if j = 0 then 1 / 2 else 0) =
      (fun _ => 0, fun _ _ => 1 / 2) := by
    unfold probabilistic_serial_phase
    ext a <;> fin_cases a <;> simp [Fin.forall_fin_two, hq, hS2, e0, e1, f0, f1] <;>
      (rename_i y; fin_cases y <;> simp [e0, e1, f0, f1])
  unfold probabilistic_serial_fractional_assignment
  simp only [Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id, p1, p2]
