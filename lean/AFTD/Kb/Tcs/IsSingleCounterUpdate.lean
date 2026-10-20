import AFTD.Prelude

/-!
# IsSingleCounterUpdate

Topic: automata   Node: 2f417e957f3e

Provenance: formalization of a published result. Source: scout/2610-23495-symmetric-two-counter-machines.md:1692

A pair of integer displacements (w₁, w₂) is a single-counter update if at least one coordinate is zero, that is, w₁ = 0 or w₂ = 0.
-/

/-- Predicate asserting that a 2-counter displacement vector has at most one non-zero coordinate. -/
def IsSingleCounterUpdate (w₁ w₂ : ℤ) : Prop := w₁ = 0 ∨ w₂ = 0
