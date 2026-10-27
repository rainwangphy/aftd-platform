import AFTD.Prelude
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# is_valid_policy_stop

Topic: online_algorithms   Node: 8ff66f1b110b

Provenance: helper lemma. step towards op184_partially_adaptive_beyond_half

For every Pandora's problem instance with deadlines `inst : PandoraDeadlineInstance`, the policy `AdaptivePolicy.stop` satisfies `IsValidPolicy inst AdaptivePolicy.stop`.
-/

/-- The stop policy AdaptivePolicy.stop is always valid for any Pandora deadline instance. -/
theorem is_valid_policy_stop (inst : PandoraDeadlineInstance) :
    IsValidPolicy inst AdaptivePolicy.stop := by
  unfold IsValidPolicy
  rw [IsValidPolicyAux.eq_1]
  trivial
