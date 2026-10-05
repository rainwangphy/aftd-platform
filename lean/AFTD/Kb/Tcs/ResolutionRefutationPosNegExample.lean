import AFTD.Prelude
import AFTD.Kb.Tcs.IsResolutionRefutation
import AFTD.Kb.Tcs.CnfLit

/-!
# resolution_refutation_pos_neg_example

Topic: proof_complexity   Node: cb166e662515

Sanity check: the formula consisting of the clauses {x_0} and {not x_0} has the resolution refutation x_0, not x_0, empty clause, of length 3.
-/

theorem resolution_refutation_pos_neg_example : is_resolution_refutation (Finset.cons ({CnfLit.pos 0} : Finset (CnfLit ℕ)) {{CnfLit.neg 0}} (by simp)) [{CnfLit.pos 0}, {CnfLit.neg 0}, ∅] := by
  refine ⟨?_, rfl⟩
  intro i
  fin_cases i
  · exact Or.inl (by simp [Finset.mem_cons])
  · exact Or.inl (by simp [Finset.mem_cons])
  · refine Or.inr (Or.inr ⟨⟨0, by simp⟩, ⟨1, by simp⟩, by simp [Fin.lt_def], by simp [Fin.lt_def], 0, ∅, ∅, ?_, ?_, ?_⟩) <;> intro l <;> simp
