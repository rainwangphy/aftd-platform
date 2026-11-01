import AFTD.Prelude

/-!
# ComparisonAlgorithm

Topic: quantum   Node: 1f633a88481e

Provenance: formalization of a published result. Source: arXiv:2610.34762 Section 2

A comparison algorithm on n objects with comparison budget c specifies, for each linear order on Fin n, an output probability distribution on Fin n.
-/

/-- A comparison algorithm on `n` objects with comparison budget `budget`. -/
structure ComparisonAlgorithm (n : ℕ) (budget : ℕ) where
  prob : LinearOrder (Fin n) → Fin n → ℝ
  nonneg : ∀ L i, 0 ≤ prob L i
  total : ∀ L, ∑ i : Fin n, prob L i = 1
