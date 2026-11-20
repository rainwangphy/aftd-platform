import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsHypotraceable

/-!
# min_order_bipartite_hypotraceable

Topic: graphs   Node: 4c6750ef8b6d

Provenance: formalization of a published result. Source: arXiv:2611.23018, Section 3, Question 8

The minimum order of a bipartite hypotraceable graph on at least 3 vertices, defined as the infimum of the set of natural numbers n such that there exists a 2-colorable simple graph G on a finite vertex type V of cardinality n with 3 ≤ n that is hypotraceable.
-/

open scoped Classical in
/-- The minimum order of a bipartite hypotraceable graph on at least 3 vertices. -/
noncomputable def min_order_bipartite_hypotraceable : ℕ := sInf {n : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : Fintype.card V = n) (G : SimpleGraph V),
    G.Colorable 2 ∧ G.IsHypotraceable ∧ 3 ≤ n}
