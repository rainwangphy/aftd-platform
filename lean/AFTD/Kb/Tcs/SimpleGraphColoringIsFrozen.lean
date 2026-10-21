import AFTD.Prelude

/-!
# simple_graph_coloring_is_frozen

Topic: graphs   Node: f8e4f2b449f0

Provenance: formalization of a published result. Source: arXiv:2610.27527 (Frozen colorings and recolorability of blowups), Sec. 1, definition of a frozen colouring

A proper colouring with colours [k] is frozen if for every vertex x and colour i, x or some neighbour of x has colour i.
-/

/-- A proper k-colouring is frozen if every vertex sees every colour in its closed neighbourhood, so no single vertex can be recoloured. -/
def simple_graph_coloring_is_frozen {W : Type*} {H : SimpleGraph W} {k : ℕ}
    (C : H.Coloring (Fin k)) : Prop :=
  ∀ (x : W) (i : Fin k), C x = i ∨ ∃ y, H.Adj x y ∧ C y = i
