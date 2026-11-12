import AFTD.Prelude
import AFTD.Kb.Tcs.GoldenBpeBias
import AFTD.Kb.Tcs.GoldenBpeBiasPoly

/-!
# golden_bpe_bias_rates_agree

Topic: algorithms   Node: 562f22fedec5

Provenance: original. Related work: knowledgebase

At the golden bias p_*, the population rate (1 - p_*)^2 / (2 - p_*) of nonoverlapping 00 pairs equals the population rate p_* * (1 - p_*) of 01 pairs.
-/

/-- At the golden bias p_*, the asymptotic nonoverlapping merge rate (1 - p_*)^2 / (2 - p_*) of pair 00 equals the rate p_*(1 - p_*) of pair 01. -/
theorem golden_bpe_bias_rates_agree :
    (1 - golden_bpe_bias) ^ 2 / (2 - golden_bpe_bias) = golden_bpe_bias * (1 - golden_bpe_bias) := by
  have hp := golden_bpe_bias_poly
  have h2 : 2 - golden_bpe_bias ≠ 0 := by
    intro h
    have h_val : golden_bpe_bias = 2 := by linarith
    nlinarith
  rw [div_eq_iff h2]
  linear_combination (1 - golden_bpe_bias) * hp
