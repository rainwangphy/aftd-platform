import AFTD.Prelude

/-!
# has_no_induced_even_cycle

Topic: graphs   Node: 5f621a8b402e

Provenance: formalization of a published result. Source: arXiv:2611.17885 Problem 2

A simple graph G contains no induced even cycle if for every even integer n ≥ 4, G contains no induced subgraph isomorphic to the cycle graph C_n.
-/

/-- A simple graph has no induced even cycle if it contains no induced cycle of length 2m with 2m ≥ 4. -/
def has_no_induced_even_cycle {V : Type*} (G : SimpleGraph V) : Prop := ∀ n : ℕ, 4 ≤ n → Even n → ¬ SimpleGraph.IsIndContained (SimpleGraph.cycleGraph n) G
