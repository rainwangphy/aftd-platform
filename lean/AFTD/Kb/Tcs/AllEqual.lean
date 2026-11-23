import AFTD.Prelude

/-!
# allEqual

Topic: quantum   Node: 4c90e9d909a1

Provenance: formalization of a published result. Source: arXiv:2611.26300

For natural numbers N and D, allEqual ι is the proposition that a vertex coloring ι : Fin N → Fin D is constant, i.e., ι v = ι w for all vertices v, w : Fin N.
-/

/-- Predicate asserting that all vertices receive the same colour. -/
def allEqual {N D : ℕ} (ι : Fin N → Fin D) : Prop := ∀ v w : Fin N, ι v = ι w
