import AFTD.Prelude

/-!
# graph_cost

Topic: algorithms   Node: d9b9366088c9

Provenance: formalization of a published result. Source: arXiv:2610.23032 Section 4

For a finite vertex type V with [Fintype V], a pairwise distance function d : V → V → ℝ, and a simple graph T on V, graph_cost d T is defined as (1/2) * ∑ u : V, ∑ v : V, if T.Adj u v then d u v else 0.
-/

/-- The total cost of a graph under distance function d. -/
noncomputable def graph_cost {V : Type*} [Fintype V] (d : V → V → ℝ) (T : SimpleGraph V) : ℝ :=
  letI : DecidableRel T.Adj := Classical.decRel _
  (1 / 2 : ℝ) * ∑ u : V, ∑ v : V, if T.Adj u v then d u v else 0
