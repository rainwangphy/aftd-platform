import AFTD.Prelude
import AFTD.Kb.Tcs.GoldenBpeBias

/-!
# golden_bpe_bias_poly

Topic: algorithms   Node: 43e7846bb522

Provenance: original. Related work: knowledgebase

The golden bias p_* satisfies the quadratic polynomial equation p_*^2 - 3 p_* + 1 = 0.
-/

/-- The golden bias p_* satisfies p_*^2 - 3 p_* + 1 = 0. -/
theorem golden_bpe_bias_poly : golden_bpe_bias ^ 2 - 3 * golden_bpe_bias + 1 = 0 := by
  unfold golden_bpe_bias
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  linear_combination (1/4 : ℝ) * h5
