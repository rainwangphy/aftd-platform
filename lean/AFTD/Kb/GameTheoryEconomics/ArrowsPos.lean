import AFTD.Prelude

/-!
# ArrowsPos

Topic: combinatorial_games   Node: b31521572d88

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

Given a type V, ArrowsPos V is the subtype of boolean-valued binary relations p : V → V → Bool that are asymmetric, meaning that for all u, v : V, if p u v is true, then p v u is false.
-/

/-- The subtype of boolean-valued binary relations on V that are asymmetric. -/
def ArrowsPos (V : Type*) : Type _ := { p : V → V → Bool // ∀ u v, p u v → ¬ p v u }
