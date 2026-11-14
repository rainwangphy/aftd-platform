import AFTD.Prelude

/-!
# nae_p_rule_strong_base_exceeds_adversary_base

Topic: quantum   Node: a634a91dc3ef

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

The explicit base 12/5 is strictly greater than 3/√2.
-/

theorem nae_p_rule_strong_base_exceeds_adversary_base :
    3 / Real.sqrt 2 < (12 / 5 : ℝ) := by
  have hspos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hs2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  apply (div_lt_iff₀ hspos).2
  nlinarith [sq_nonneg (12 * Real.sqrt 2 - 15)]
