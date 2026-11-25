import AFTD.Prelude

/-!
# Multigraph

Topic: graphs   Node: 7652fe63897d

Provenance: formalization of a published result. Source: scout/2611-29111-when-do-local-bounds-permit-optimal-edge-colorings.md:87

A loopless multigraph on a vertex type V, represented by a symmetric edge-multiplicity function mult with mult v v = 0.
-/

/-- A loopless multigraph represented by a symmetric edge multiplicity function mult. -/
structure Multigraph (V : Type*) where
  mult : V → V → ℕ
  symm : ∀ u v, mult u v = mult v u
  loopless : ∀ v, mult v v = 0
