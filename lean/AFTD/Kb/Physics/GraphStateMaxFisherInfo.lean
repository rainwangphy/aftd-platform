import AFTD.Prelude
import AFTD.Kb.Physics.GraphStateFisherInfo

/-!
# graph_state_max_fisher_info

Topic: quantum_mechanics   Node: 28f91909733c

Provenance: formalization of a published result. Source: arXiv:2611.08593

For natural numbers n and m, graph_state_max_fisher_info n m is the supremum of the collective-X quantum Fisher information graph_state_fisher_info G over all connected triangle-free simple graphs G on Fin n with exactly m edges.
-/

/-- The maximum collective-X quantum Fisher information over all connected triangle-free simple graphs on n vertices with m edges. -/
noncomputable def graph_state_max_fisher_info (n m : ℕ) : ℕ := open scoped Classical in
  Finset.sup
    (Finset.filter (fun G : SimpleGraph (Fin n) =>
      G.Connected ∧ G.CliqueFree 3 ∧ G.edgeFinset.card = m) Finset.univ)
    (fun G => graph_state_fisher_info G)
