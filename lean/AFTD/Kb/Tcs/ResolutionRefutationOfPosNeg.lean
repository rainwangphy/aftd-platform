import AFTD.Prelude
import AFTD.Kb.Tcs.IsResolutionRefutation
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.IsResolutionDerivation

/-!
# resolution_refutation_of_pos_neg

Topic: proof_complexity   Node: 4f351e2626bf

Provenance: helper lemma. step towards resolution_fpt_incidence_treewidth

Base case for unit contradiction: a formula containing complementary unit clauses {x} and {not x} admits a resolution refutation of length at most 3.
-/

/-- A formula containing complementary unit literals admits a resolution refutation of length at most 3. -/
theorem resolution_refutation_of_pos_neg {V : Type*} [DecidableEq V] (F : Finset (Finset (CnfLit V))) (x : V) (hpos : {CnfLit.pos x} ∈ F) (hneg : {CnfLit.neg x} ∈ F) : ∃ π : List (Finset (CnfLit V)), is_resolution_refutation F π ∧ π.length ≤ 3 := by
  refine ⟨[{CnfLit.pos x}, {CnfLit.neg x}, ∅], ⟨?_, rfl⟩, by simp⟩
  intro i
  fin_cases i
  · exact Or.inl hpos
  · exact Or.inl hneg
  · refine Or.inr (Or.inr ⟨⟨0, by simp⟩, ⟨1, by simp⟩, by simp [Fin.lt_def],
      by simp [Fin.lt_def], x, ∅, ∅, ?_, ?_, ?_⟩) <;> intro l <;> simp
