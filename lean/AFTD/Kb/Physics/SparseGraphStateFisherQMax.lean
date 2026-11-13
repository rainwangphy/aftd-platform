import AFTD.Prelude
import AFTD.Kb.Physics.GraphStateFisherQ

/-!
# sparse_graph_state_fisher_q_max

Topic: quantum_mechanics   Node: 1b82d272a475

Provenance: original. Related work: arXiv:2611.08593

For positive integers n, d, c, Q_max(n, d, c) is the maximum of Q(G) over all connected triangle-free graphs G on n vertices with d*n + c edges.
-/

/-- The maximum collective-X quantum Fisher information Q(G) over connected triangle-free n-vertex graphs with d*n+c edges. -/
noncomputable def sparse_graph_state_fisher_q_max (n d c : ℕ) : ℕ :=
  sSup { q | ∃ (G : SimpleGraph (Fin n)), G.Connected ∧ G.CliqueFree 3 ∧
    Nat.card G.edgeSet = d * n + c ∧ q = graph_state_fisher_q G }
