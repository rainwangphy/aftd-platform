import AFTD.Prelude
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.PandoraDeadlineInstance

/-!
# expected_utility_dus_stop

Topic: online_algorithms   Node: 426ef7f287a5

Provenance: helper lemma. step towards op184_partially_adaptive_beyond_half

For any Pandora deadline instance `inst`, the expected net utility `expectedUtilityDUS inst AdaptivePolicy.stop` is zero.
-/

/-- The expected net utility of the stop policy under deferred-until-stopping commitment is zero. -/
theorem expected_utility_dus_stop (inst : PandoraDeadlineInstance) :
    expectedUtilityDUS inst AdaptivePolicy.stop = 0 := by
  rfl
