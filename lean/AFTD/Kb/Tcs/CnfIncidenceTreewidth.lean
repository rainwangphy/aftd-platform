import AFTD.Prelude
import AFTD.Kb.Tcs.GraphTreewidth
import AFTD.Kb.Tcs.CnfIncidenceGraph
import AFTD.Kb.Tcs.CnfLit

/-!
# cnf_incidence_treewidth

Topic: proof_complexity   Node: 15c8b37b1b33

The incidence treewidth tw*(F) of a CNF formula F: the treewidth of its incidence graph.
-/

/-- The incidence treewidth of a CNF formula. -/
noncomputable def cnf_incidence_treewidth {V : Type*} [DecidableEq V] (F : Finset (Finset (CnfLit V))) : ℕ :=
  graph_treewidth (cnf_incidence_graph F)
