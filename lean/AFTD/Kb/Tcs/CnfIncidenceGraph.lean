import AFTD.Prelude
import AFTD.Kb.Tcs.CnfVars
import AFTD.Kb.Tcs.CnfLitVar
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_incidence_graph

Topic: proof_complexity   Node: ecd3a348a937

Provenance: formalization of a published result. Source: Short Resolution Refutations for CNFs with Bounded Weighted Incidence Treewidth, arXiv:2610.02047, Sec. 3.2 (incidence graph of a CNF formula)

The incidence graph G*(F) of a CNF formula F: the bipartite graph whose vertices are the variables of F and the clauses of F, a variable x adjacent to a clause C iff x occurs in C.
-/

/-- The incidence graph of a CNF formula. -/
def cnf_incidence_graph {V : Type*} [DecidableEq V] (F : Finset (Finset (CnfLit V))) : SimpleGraph ({x // x ∈ cnf_vars F} ⊕ {C // C ∈ F}) :=
  SimpleGraph.fromRel fun a b =>
    match a, b with
    | Sum.inl x, Sum.inr C => ∃ l ∈ C.1, cnf_lit_var l = x.1
    | _, _ => False
