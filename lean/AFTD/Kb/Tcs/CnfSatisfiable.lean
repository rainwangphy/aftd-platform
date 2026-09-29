import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# CnfSatisfiable

Topic: np_completeness   Node: ff407c555510

A CNF formula (a list of clauses, each a list of literals) is satisfiable if there is a truth assignment such that every clause contains at least one true literal.
-/

/-- A CNF formula is satisfiable if there exists a truth assignment satisfying at least one literal in each clause. -/
def CnfSatisfiable {V : Type*} (f : List (List (CnfLit V))) : Prop := ∃ τ : V → Bool, ∀ c ∈ f, ∃ l ∈ c, match l with
    | CnfLit.pos v => τ v = true
    | CnfLit.neg v => τ v = false
