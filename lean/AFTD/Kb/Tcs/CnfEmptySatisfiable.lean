import AFTD.Prelude
import AFTD.Kb.Tcs.CnfSatisfiable

/-!
# cnf_empty_satisfiable

Topic: np_completeness   Node: d137c24fc135

Provenance: formalization of a published result. Source: standard textbook result (propositional logic: the empty CNF is satisfiable)

The empty CNF formula has no clauses to satisfy, hence is satisfiable under any truth assignment.
-/

/-- The empty CNF formula is vacuously satisfiable. -/
theorem cnf_empty_satisfiable (V : Type*) : CnfSatisfiable (V := V) [] := ⟨fun _ => true, fun _ h => nomatch h⟩
