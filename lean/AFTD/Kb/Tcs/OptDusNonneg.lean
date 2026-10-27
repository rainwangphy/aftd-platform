import AFTD.Prelude
import AFTD.Kb.Tcs.ExpectedUtilityDusLeOptDus
import AFTD.Kb.Tcs.IsValidPolicyStop
import AFTD.Kb.Tcs.ExpectedUtilityDusStop
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.OptDUS
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# opt_dus_nonneg

Topic: online_algorithms   Node: 11aced82909d

Provenance: helper lemma. step towards op184_partially_adaptive_beyond_half

For any Pandora deadline instance `inst`, `0 ≤ optDUS inst`.
-/

/-- The optimal expected utility under deferred-until-stopping commitment is non-negative. -/
theorem opt_dus_nonneg (inst : PandoraDeadlineInstance) :
    0 ≤ optDUS inst := by
  rw [← expected_utility_dus_stop inst]
  exact expected_utility_dus_le_opt_dus inst _ (is_valid_policy_stop inst)
