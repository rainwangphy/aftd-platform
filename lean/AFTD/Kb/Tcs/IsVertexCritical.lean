import AFTD.Prelude

/-!
# is_vertex_critical

Topic: graphs   Node: 5e0fa7a2f740

Provenance: formalization of a published result. Source: arXiv:2610.40279 Section 1

A simple graph G is k-vertex-critical if its chromatic number is k and deleting any vertex yields a graph with chromatic number strictly less than k.
-/

/-- A graph is k-vertex-critical if its chromatic number is k and deleting any vertex strictly reduces its chromatic number. -/
def is_vertex_critical {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  G.chromaticNumber = (k : ℕ∞) ∧ ∀ v : V, (G.induce ({v}ᶜ : Set V)).chromaticNumber < (k : ℕ∞)
