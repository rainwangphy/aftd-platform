import AFTD.Prelude
import AFTD.Kb.Tcs.DfaStateComplexity

/-!
# dfa_state_complexity_empty

Topic: automata   Node: bfeb3d34d0e4

Provenance: helper lemma. folklore

For any alphabet α, the deterministic state complexity of the empty language 0 is at most 1.
-/

/-- The empty language over any alphabet has DFA state complexity at most 1. -/
theorem dfa_state_complexity_empty (α : Type*) : dfa_state_complexity (0 : Language α) ≤ 1 := by
  apply Nat.sInf_le
  refine ⟨Unit, inferInstance, ⟨fun _ _ => (), (), ∅⟩, Fintype.card_unit, ?_⟩
  ext x
  simp [DFA.mem_accepts]
