import AFTD.Prelude
import AFTD.Kb.Tcs.DigitExchangeWalshLimit

/-!
# op_1608_digit_exchange_walsh_limit_sum_one

Topic: cryptography   Node: a6c4665491c1

Provenance: original. Related work: arXiv:2611.02572

The sum of the seven conjectured limiting probabilities digit_exchange_walsh_limit j for j in Finset.range 7 equals 1.
-/

/-- Normalization of the symmetric six Walsh limit law: the seven probabilities sum to 1. -/
theorem op_1608_digit_exchange_walsh_limit_sum_one :
    ∑ j ∈ Finset.range 7, digit_exchange_walsh_limit j = 1 := by
  norm_num [Finset.sum_range_succ, digit_exchange_walsh_limit]
