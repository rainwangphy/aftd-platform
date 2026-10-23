import AFTD.Prelude
import AFTD.Kb.Tcs.IsResolutionRefutation
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.IsResolutionDerivation

/-!
# resolution_refutation_of_empty_mem

Topic: proof_complexity   Node: 7f78d836e62d

Provenance: helper lemma. step towards resolution_fpt_incidence_treewidth

Base case: if a formula contains the empty clause, it admits a resolution refutation of length 1 (namely [∅]).
-/

/-- A CNF formula containing the empty clause has a 1-step resolution refutation. -/
theorem resolution_refutation_of_empty_mem (F : Finset (Finset (CnfLit ℕ))) (h : ∅ ∈ F) : ∃ π : List (Finset (CnfLit ℕ)), is_resolution_refutation F π ∧ π.length = 1 := by
  refine ⟨[∅], ⟨?_, rfl⟩, rfl⟩
  intro i
  left
  cases i with
  | mk val isLt =>
    simp only [List.length_singleton] at isLt
    interval_cases val
    exact h
