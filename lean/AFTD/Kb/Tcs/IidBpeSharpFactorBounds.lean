import AFTD.Prelude
import AFTD.Kb.Tcs.IidBpeSharpFactor

/-!
# iid_bpe_sharp_factor_bounds

Topic: algorithms   Node: 7ff2a4bace45

Provenance: helper lemma. folklore

The i.i.d. BPE sharp approximation constant c = (2 + √2)/4 lies strictly in the open unit interval (0, 1).
-/

/-- The i.i.d. BPE sharp approximation constant c = (2 + √2)/4 lies strictly between 0 and 1. -/
theorem iid_bpe_sharp_factor_bounds : 0 < iid_bpe_sharp_factor ∧ iid_bpe_sharp_factor < 1 := by
  unfold iid_bpe_sharp_factor
  constructor
  · positivity
  · have : Real.sqrt 2 < 2 := by
      rw [Real.sqrt_lt' (by norm_num)]
      norm_num
    linarith
