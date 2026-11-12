import AFTD.Prelude

/-!
# IsASPath

Topic: combinatorics   Node: 2ed658b4e7a0

Provenance: formalization of a published result. Source: arXiv:2611.12329 Piercing a Chessboard with Restricted Slopes, Eq. (1)

An ascending shallow (AS) path coordinate function a : ℤ → ℤ satisfies 0 ≤ a(t+1) - a(t) ≤ 1 and a(t+2) ≥ a(t) + 1 for all t ∈ ℤ.
-/

/-- Predicate for an ascending shallow (AS) path coordinate function a : ℤ → ℤ. -/
def IsASPath (a : ℤ → ℤ) : Prop := ∀ t : ℤ, 0 ≤ a (t + 1) - a t ∧ a (t + 1) - a t ≤ 1 ∧ a t + 1 ≤ a (t + 2)
