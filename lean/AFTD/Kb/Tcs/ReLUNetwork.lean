import AFTD.Prelude
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# ReLUNetwork

Topic: np_completeness   Node: 11202589f8fc

Provenance: formalization of a published result. Source: arXiv:2610.06092, Section 2.1

A feedforward ReLU neural network from the real line to the real line with hidden layers of width k, specified by rational affine input and output layers and an arbitrary sequence of width-k hidden layers.
-/

/-- A feedforward ReLU neural network from ℝ to ℝ with hidden layer width k and rational weights and biases. -/
structure ReLUNetwork (k : ℕ) where
  in_weight : Fin k → ℚ
  in_bias : Fin k → ℚ
  layers : List (ReLUHiddenLayer k)
  out_weight : Fin k → ℚ
  out_bias : ℚ
