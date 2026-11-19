import AFTD.Prelude
import AFTD.Kb.Tcs.CnfLit

/-!
# ThrCond

Topic: proof_complexity   Node: ce6c3ab802f6

Provenance: formalization of a published result. Source: arXiv:2611.24548 Definition 2.12

A threshold condition over n Boolean variables is an inequality f ≥ s, where f is a nonnegative integer linear combination of literals (given by coefficients CnfLit (Fin n) → ℕ) and s is an integer threshold.
-/

/-- A threshold condition f ≥ s over n Boolean variables, where f is a nonnegative linear combination of literals. -/
structure ThrCond (n : ℕ) where
  coeffs : CnfLit (Fin n) → ℕ
  threshold : ℤ
