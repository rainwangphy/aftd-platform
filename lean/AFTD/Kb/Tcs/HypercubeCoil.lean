import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHypercube

/-!
# hypercube_coil

Topic: combinatorics   Node: dcec85366883

Provenance: formalization of a published result. Source: arXiv:2610.36461 Section 1

A subset S of vertices in the hypercube Q_n is a coil if it has size at least 4 and its induced subgraph is isomorphic to a cycle graph of size |S|.
-/

/-- A coil in the n-dimensional hypercube is an induced cycle of length at least 4. -/
def hypercube_coil (n : ℕ) (S : Finset (Fin n → Bool)) : Prop :=
  4 ≤ S.card ∧ Nonempty (((simple_graph_hypercube n).induce (S : Set (Fin n → Bool))) ≃g SimpleGraph.cycleGraph S.card)
