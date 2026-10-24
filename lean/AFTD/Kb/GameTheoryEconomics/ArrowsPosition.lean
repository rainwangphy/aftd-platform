import AFTD.Prelude

/-!
# ArrowsPosition

Topic: combinatorial_games   Node: e6fab6b94e95

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

A position in the Game of Arrows on a simple graph G consists of a finite set of directed edges (arrows) between vertices adjacent in G, such that no edge is directed in both orientations.
-/

/-- A position in the Game of Arrows on a simple graph G: a finset of directed edges that are adjacent in G and asymmetric. -/
structure ArrowsPosition (V : Type) (G : SimpleGraph V) where
  arrows : Finset (V × V)
  arrows_sub : ∀ {e}, e ∈ arrows → G.Adj e.1 e.2
  arrows_asymm : ∀ {u v}, (u, v) ∈ arrows → (v, u) ∉ arrows
