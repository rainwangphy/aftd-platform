import AFTD.Prelude

/-!
# is_list_colorable

Topic: graphs   Node: 8c2f89f9996b

Provenance: formalization of a published result. Source: arXiv:2611.25850: Section 1

A simple graph G on vertex type V is colorable from a finite list assignment L : V → Finset κ if there exists a proper coloring c : G.Coloring κ such that c(v) ∈ L(v) for all v : V.
-/

/-- A graph is colorable from a finite list assignment L. -/
def is_list_colorable {V κ : Type*} (G : SimpleGraph V) (L : V → Finset κ) : Prop := ∃ c : G.Coloring κ, ∀ v, c v ∈ L v
