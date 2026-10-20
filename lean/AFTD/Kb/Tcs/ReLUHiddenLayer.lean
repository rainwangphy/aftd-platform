import AFTD.Prelude

/-!
# ReLUHiddenLayer

Topic: np_completeness   Node: 7fa4094d7513

Provenance: formalization of a published result. Source: arXiv:2610.06092, Section 2.1

A hidden layer of width k consists of a k-by-k rational weight matrix and a rational bias vector of length k.
-/

/-- A hidden layer of width k in a ReLU neural network with rational weights and biases. -/
structure ReLUHiddenLayer (k : ℕ) where
  weight : Fin k → Fin k → ℚ
  bias : Fin k → ℚ
