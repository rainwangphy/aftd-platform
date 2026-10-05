import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLitVar
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_vars

Topic: proof_complexity   Node: aef5910fe5e7

The set var(F) of variables occurring in a CNF formula F, given as a finite set of clauses, each a finite set of literals.
-/

/-- The variables of a CNF formula given as a finite set of clauses, each a finite set of literals. -/
def cnf_vars {V : Type*} [DecidableEq V] (F : Finset (Finset (CnfLit V))) : Finset V :=
  F.biUnion fun C => C.image cnf_lit_var
