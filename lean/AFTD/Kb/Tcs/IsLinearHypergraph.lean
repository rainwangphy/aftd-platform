import AFTD.Prelude

/-!
# is_linear_hypergraph

Topic: combinatorics   Node: 20b896618542

Provenance: formalization of a published result. Source: arXiv:2610.14829 Section 2

A hypergraph F is linear if any two distinct hyperedges in F intersect in at most one vertex.
-/

/-- A hypergraph is linear if any two distinct hyperedges intersect in at most one vertex. -/
def is_linear_hypergraph {V : Type*} [DecidableEq V] (F : Finset (Finset V)) : Prop :=
  ∀ e₁ ∈ F, ∀ e₂ ∈ F, e₁ ≠ e₂ → (e₁ ∩ e₂).card ≤ 1
