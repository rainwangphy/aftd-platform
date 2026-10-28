import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsBElement
import AFTD.Kb.LogicFoundations.BmiIsMElement
import AFTD.Kb.LogicFoundations.BmiIsIElement
import AFTD.Kb.LogicFoundations.BmiIsYElement

/-!
# bmi_elements_satisfiable

Topic: proof_theory   Node: 704e8c7ac8fe

Provenance: helper lemma. folklore

There exists a magma with an element that is simultaneously a $B$-element, an $M$-element, an $I$-element, and a $Y$-element (witnessed by the one-element magma).
-/

/-- The one-element magma has an element that is simultaneously a B-, M-, I-, and Y-element. -/
theorem bmi_elements_satisfiable : ∃ (A : Type) (_ : Mul A) (e : A),
    bmi_is_b_element e ∧ bmi_is_m_element e ∧ bmi_is_i_element e ∧ bmi_is_y_element e := ⟨Unit, inferInstance, (), fun _ _ _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
