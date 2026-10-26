import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraThresholdPolicy
import AFTD.Kb.Tcs.PandoraDeadlineFeasible
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# pandora_threshold_policy_nil

Topic: online_algorithms   Node: 0f80d4bff331

Provenance: helper lemma. Sanity lemma for the definitions of arXiv:2610.13775 Section 3

Sanity: the threshold policy on the empty list stops at once.
-/

theorem pandora_threshold_policy_nil {n : ℕ} (t : ℝ) :
    pandora_threshold_policy ([] : List (Fin n)) t = .stop := rfl
