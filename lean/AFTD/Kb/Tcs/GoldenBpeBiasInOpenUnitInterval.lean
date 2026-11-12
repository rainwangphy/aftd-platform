import AFTD.Prelude
import AFTD.Kb.Tcs.GoldenBpeBias

/-!
# golden_bpe_bias_in_open_unit_interval

Topic: algorithms   Node: 246a6fc60ef8

Provenance: original. Related work: knowledgebase

The golden bias p_* lies strictly in the open unit interval (0, 1).
-/

/-- The golden bias p_* satisfies 0 < p_* and p_* < 1. -/
theorem golden_bpe_bias_in_open_unit_interval :
    0 < golden_bpe_bias ∧ golden_bpe_bias < 1 := by
  unfold golden_bpe_bias
  have h1 : (1 : ℝ) < Real.sqrt 5 := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h2 : Real.sqrt 5 < 3 := by
    have : (3 : ℝ) = Real.sqrt 9 := by norm_num
    rw [this]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  constructor
  · linarith
  · linarith
