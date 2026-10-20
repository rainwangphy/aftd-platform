import AFTD.Prelude

/-!
# relu

Topic: np_completeness   Node: 8dce75dff974

Provenance: formalization of a published result. Source: arXiv:2610.06092, Section 2.1

The rectified linear unit (ReLU) activation function maps each real number x to max(x, 0).
-/

/-- The Rectified Linear Unit (ReLU) activation function, defined by relu(x) = max(x, 0). -/
def relu (x : ℝ) : ℝ := max x 0
