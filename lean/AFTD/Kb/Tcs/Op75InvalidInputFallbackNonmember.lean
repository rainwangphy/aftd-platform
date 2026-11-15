import AFTD.Prelude
import AFTD.Kb.Tcs.ReluWidth3LanguageMemIff
import AFTD.Kb.Tcs.Op75CompactNetworkSubsetSum
import AFTD.Kb.Tcs.Op75Subset
import AFTD.Kb.Tcs.ReluWidth3UnitIntervalZeroLanguage
import AFTD.Kb.Tcs.ReluNetworkHasUnitIntervalZero
import AFTD.Kb.Tcs.ReluNetwork3Encode
import AFTD.Kb.Tcs.Op75CompactNetwork

/-!
# op75_invalid_input_fallback_nonmember

Topic: np_completeness   Node: 06acb0d7d4fc

Provenance: helper lemma. OP-75: fixed output for malformed subset-sum inputs.

The encoding of the empty-weight target-one network is a no-instance of the width-three unit-interval zero language.
-/

theorem op75_invalid_input_fallback_nonmember : relu_network3_encode (op75_compact_network [] 1) ∉ relu_width3_unit_interval_zero_language := by
  rw [relu_width3_language_mem_iff, op75_compact_network_subset_sum]
  simp [op75_subset]
