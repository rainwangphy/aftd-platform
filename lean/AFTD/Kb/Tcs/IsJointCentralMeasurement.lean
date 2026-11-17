import AFTD.Prelude

/-!
# IsJointCentralMeasurement

Topic: quantum   Node: 00eb0fe23e55

Provenance: formalization of a published result. Source: arXiv:2610.35838 Sec. II.3

A joint quantum measurement on ℂ^m yielding signs f₀, f₁ ∈ {-1, 1} is represented by a four-element POVM M indexed by Fin 2 × Fin 2 of positive semidefinite matrices summing to the identity.
-/

/-- A joint central measurement with binary signs is a 4-outcome POVM summing to identity. -/
def IsJointCentralMeasurement {m : ℕ} (M : Fin 2 → Fin 2 → Matrix (Fin m) (Fin m) ℂ) : Prop := (∀ s0 s1, (Matrix.toEuclideanLin (M s0 s1)).IsPositive) ∧
  (∑ s0 : Fin 2, ∑ s1 : Fin 2, M s0 s1 = 1)
