import AFTD.Prelude

/-!
# SzfMultiForced

Topic: graphs   Node: b451b94845e0

Provenance: formalization of a published result. Source: arXiv:2611.15741 Section 1 (skew colour change rule on multigraphs, adjacency counted with multiplicity)

Skew zero forcing on a multigraph with adjacency multiplicities μ (μ u v = number of edges between u and v, μ u u = number of loops at u): a vertex is forced from the initial filled set S if it lies in S, or if for some vertex u (filled or not) it is the only unfilled neighbour of u counted with multiplicity, i.e. μ u w = 1 and every other neighbour x of u (μ u x ≠ 0, x ≠ w) is already forced.
-/

/-- Skew zero forcing on a multigraph given by adjacency multiplicities `μ` (loops: `μ u u`). -/
inductive SzfMultiForced {V : Type*} (μ : V → V → ℕ) (S : Set V) : V → Prop where
  | init (v : V) : v ∈ S → SzfMultiForced μ S v
  | step (u w : V) :
      μ u w = 1 →
      (∀ x, x ≠ w → μ u x ≠ 0 → SzfMultiForced μ S x) →
      SzfMultiForced μ S w
