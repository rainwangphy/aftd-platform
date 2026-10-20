import AFTD.Prelude
import AFTD.Kb.Tcs.Relu

/-!
# relu_nonneg

Topic: np_completeness   Node: 45fd14772771

Provenance: helper lemma. folklore

For any real number x, relu(x) is greater than or equal to zero.
-/

/-- The ReLU activation function is always non-negative. -/
theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := le_max_right x 0
