import AFTD.Prelude
import AFTD.Kb.Tcs.CnfSatisfiable
import AFTD.Kb.Tcs.CnfSatisfiableSubset
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_satisfiable_of_append

Topic: np_completeness   Node: ad3d753e32cf

If the concatenation `f1 ++ f2` of two CNF formulas is satisfiable (`CnfSatisfiable (f1 ++ f2)`), then both `f1` and `f2` are satisfiable (`CnfSatisfiable f1 ∧ CnfSatisfiable f2`).
-/

/-- If a concatenated CNF formula f1 ++ f2 is satisfiable, then both f1 and f2 are satisfiable. -/
theorem cnf_satisfiable_of_append {V : Type*} {f1 f2 : List (List (CnfLit V))} (h : CnfSatisfiable (f1 ++ f2)) : CnfSatisfiable f1 ∧ CnfSatisfiable f2 := ⟨cnf_satisfiable_subset (List.subset_append_left f1 f2) h, cnf_satisfiable_subset (List.subset_append_right f1 f2) h⟩
