import AFTD.Prelude
import AFTD.Kb.Tcs.CnfSatisfiable
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_not_satisfiable_of_has_empty_clause

Topic: np_completeness   Node: 200a95af7c81

Provenance: formalization of a published result. Source: standard textbook result (propositional logic: a CNF containing the empty clause is unsatisfiable)

A CNF formula containing the empty clause cannot be satisfied by any assignment because the empty clause contains no literals to be made true.
-/

/-- Any CNF formula containing an empty clause is unsatisfiable. -/
theorem cnf_not_satisfiable_of_has_empty_clause {V : Type*} (f : List (List (CnfLit V))) (h : [] ∈ f) : ¬ CnfSatisfiable f := by
  rintro ⟨τ, hτ⟩
  obtain ⟨l, hl, -⟩ := hτ [] h
  exact List.not_mem_nil hl
