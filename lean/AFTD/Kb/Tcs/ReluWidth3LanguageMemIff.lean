import AFTD.Prelude
import AFTD.Kb.Tcs.ReluWidth3UnitIntervalZeroLanguage
import AFTD.Kb.Tcs.ReluNetwork3EncodeInjective
import AFTD.Kb.Tcs.ReLUNetwork
import AFTD.Kb.Tcs.ReluNetwork3Encode
import AFTD.Kb.Tcs.ReluNetworkHasUnitIntervalZero

/-!
# relu_width3_language_mem_iff

Topic: np_completeness   Node: 9e6fbcc1fe14

Provenance: helper lemma. Sanity lemma for relu_width3_unit_interval_zero_language, serving OP-75 (arXiv:2610.06092, Remark 5.15).

Sanity check of the language: the encoding of a width-3 ReLU network lies in the verification language exactly when the network has a zero in [0, 1].
-/

theorem relu_width3_language_mem_iff (net : ReLUNetwork 3) :
    relu_network3_encode net ∈ relu_width3_unit_interval_zero_language ↔
      relu_network_has_unit_interval_zero net := by
  constructor
  · rintro ⟨n, e, hz⟩
    rwa [← relu_network3_encode_injective e]
  · intro hz
    exact ⟨net, rfl, hz⟩
