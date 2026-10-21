import AFTD.Prelude
import AFTD.Kb.Tcs.GraphCost

/-!
# is_mst

Topic: algorithms   Node: 42d19c73af1a

Provenance: formalization of a published result. Source: arXiv:2610.23032 Section 4

A simple graph T on a finite type V is a minimum spanning tree under d : V → V → ℝ if T is a tree (T.IsTree) and graph_cost d T ≤ graph_cost d T' for every tree T' on V.
-/

/-- A simple graph is a minimum spanning tree if it is a tree and minimizes graph_cost. -/
def is_mst {V : Type*} [Fintype V] (d : V → V → ℝ) (T : SimpleGraph V) : Prop :=
  T.IsTree ∧ ∀ T' : SimpleGraph V, T'.IsTree → graph_cost d T ≤ graph_cost d T'
