import AFTD.Prelude
import AFTD.Kb.Physics.SparseGraphStateFisherCoreK
import AFTD.Kb.Physics.IsMarkedCoreGraph
import AFTD.Kb.Physics.GraphStateFisherQ

/-!
# core_constant_b

Topic: quantum_mechanics   Node: 10d53544790d

Provenance: original. Related work: arXiv:2611.08593

For natural numbers d and c, let k = sparse_graph_state_fisher_core_k d c. The core constant B(d, c) is the supremum of Q(J) - 1 over all pairs (J, s) of a graph J on Fin (k + 1) and a vertex s satisfying is_marked_core_graph k d c J s.
-/

/-- The core constant B(d, c), defined as the supremum of Q(J) - 1 over all marked core graphs (J, s) on k(d, c)+1 vertices. -/
noncomputable def core_constant_b (d c : ℕ) : ℕ :=
  let k := sparse_graph_state_fisher_core_k d c
  sSup { b | ∃ (J : SimpleGraph (Fin (k + 1))) (s : Fin (k + 1)),
    is_marked_core_graph k d c J s ∧ b = graph_state_fisher_q J - 1 }
