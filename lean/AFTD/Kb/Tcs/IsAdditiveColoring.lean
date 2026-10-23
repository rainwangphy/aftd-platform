import AFTD.Prelude

/-!
# is_additive_coloring

Topic: graphs   Node: 44cf9ce13311

Provenance: formalization of a published result. Source: arXiv:2610.30174, Section 1

An additive coloring of a finite simple graph G is a vertex labeling f : V → ℕ with positive integers such that for every edge {u, v}, the sum of labels in the neighborhood of u differs from the sum of labels in the neighborhood of v.
-/

/-- An additive coloring of a graph assigns positive integers to vertices such that adjacent vertices have distinct neighborhood sums. -/
def is_additive_coloring {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (f : V → ℕ) : Prop :=
  (∀ v, 0 < f v) ∧
    ∀ ⦃u v : V⦄, G.Adj u v →
      ∑ w ∈ G.neighborFinset u, f w ≠ ∑ w ∈ G.neighborFinset v, f w
