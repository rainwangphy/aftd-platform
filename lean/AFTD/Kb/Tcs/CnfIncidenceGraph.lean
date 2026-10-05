import AFTD.Prelude
import AFTD.Kb.Tcs.CnfVars
import AFTD.Kb.Tcs.CnfLitVar
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_incidence_graph

Topic: proof_complexity   Node: ecd3a348a937

The incidence graph G*(F) of a CNF formula F: the bipartite graph whose vertices are the variables of F and the clauses of F, a variable x adjacent to a clause C iff x occurs in C.
-/

/-- The incidence graph of a CNF formula. -/
def cnf_incidence_graph {V : Type*} [DecidableEq V] (F : Finset (Finset (CnfLit V))) : SimpleGraph ({x // x ∈ cnf_vars F} ⊕ {C // C ∈ F}) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | Sum.inl x, Sum.inr C => ∃ l ∈ C.1, cnf_lit_var l = x.1
    | _, _ => False
