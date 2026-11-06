import AFTD.Prelude

/-!
# CubeFunc

Topic: submodular   Node: dcbab84f383e

Provenance: formalization of a published result. Source: arXiv:2611.02374, Sec. 1.2

The type of functions from the n-dimensional Boolean hypercube {0, 1}^n into {0, 1, ..., k}, represented by Fin (k + 1).
-/

/-- The type of functions from the n-dimensional Boolean hypercube {0, 1}^n into {0, 1, ..., k}. -/
abbrev CubeFunc (n k : ℕ) : Type := (Fin n → Bool) → Fin (k + 1)
