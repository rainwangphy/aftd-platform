import AFTD.Prelude
import AFTD.Kb.Tcs.IsPovm

/-!
# is_povm_one_outcome

Topic: quantum   Node: 19d5230aacf4

Provenance: helper lemma. Sanity lemma for is_povm.

Sanity check of is_povm: the one-outcome family consisting of the identity is a POVM.
-/

theorem is_povm_one_outcome : is_povm 1 (fun _ : Unit => (1 : Matrix (Fin 1) (Fin 1) ℂ)) := by
  open scoped ComplexOrder in exact ⟨fun _ => Matrix.PosSemidef.one, by simp⟩
