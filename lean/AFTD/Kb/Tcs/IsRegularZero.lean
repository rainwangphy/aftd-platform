import AFTD.Prelude

/-!
# is_regular_zero

Topic: automata   Node: b198789f8cee

Provenance: formalization of a published result. Source: standard textbook result (automata theory: the empty language is regular)

The empty language is regular.
-/

/-- The empty language is regular. -/
theorem is_regular_zero {α : Type*} : (0 : Language α).IsRegular := ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, by
  ext x
  simp [DFA.mem_accepts]⟩
