import AFTD.Prelude
import AFTD.Kb.Tcs.CnfSatisfiable
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_satisfiable_subset

Topic: np_completeness   Node: 57afb2fcb24e

If every clause of a CNF formula `f1` is contained in a CNF formula `f2` (that is, `f1 ⊆ f2`), and `f2` is satisfiable (`CnfSatisfiable f2`), then `f1` is also satisfiable (`CnfSatisfiable f1`).
-/

/-- Subformula monotonicity: any subformula (subset of clauses) of a satisfiable CNF formula is satisfiable. -/
theorem cnf_satisfiable_subset {V : Type*} {f1 f2 : List (List (CnfLit V))}
    (hsub : f1 ⊆ f2) (hsat : CnfSatisfiable f2) : CnfSatisfiable f1 := by
  obtain ⟨τ, hτ⟩ := hsat
  exact ⟨τ, fun c hc => hτ c (hsub hc)⟩
