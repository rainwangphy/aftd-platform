import AFTD.Prelude
import AFTD.Kb.Tcs.PauliLabel
import AFTD.Kb.Tcs.ApplyCliffordGate
import AFTD.Kb.Tcs.CliffordGate

/-!
# apply_clifford_gate_cnot_involutive

Topic: quantum   Node: 45f903314f5b

Provenance: helper lemma. step towards op_757_all_to_all_cnot_lower_bound

The CNOT gate action on Pauli labels is an involution.
-/

/-- The CNOT gate action on Pauli labels is an involution. -/
theorem apply_clifford_gate_cnot_involutive {k : ℕ} (c t : Fin k) (hct : c ≠ t) (p : PauliLabel k) :
    apply_clifford_gate (.cnot c t hct) (apply_clifford_gate (.cnot c t hct) p) = p := by
  dsimp [apply_clifford_gate]
  ext i
  · dsimp only
    have h1 : Function.update p.1 t (p.1 t + p.1 c) c = p.1 c := Function.update_of_ne hct (p.1 t + p.1 c) p.1
    rw [h1]
    by_cases hi : i = t
    · subst hi
      simp [add_assoc, CharTwo.add_self_eq_zero]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  · dsimp only
    have h2 : Function.update p.2 c (p.2 c + p.2 t) t = p.2 t := Function.update_of_ne hct.symm (p.2 c + p.2 t) p.2
    rw [h2]
    by_cases hi : i = c
    · subst hi
      simp [add_assoc, CharTwo.add_self_eq_zero]
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
