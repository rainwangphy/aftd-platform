import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraThresholdPolicy
import AFTD.Kb.Tcs.PandoraDeadlineFeasible
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# pandora_threshold_policy_cons

Topic: online_algorithms   Node: 10398f45574b

Provenance: helper lemma. Sanity lemma for the definitions of arXiv:2610.13775 Section 3

Sanity: the threshold policy on b :: rest opens b, stops if its value exceeds t, and otherwise continues with the threshold policy on rest.
-/

theorem pandora_threshold_policy_cons {n : ℕ} (b : Fin n) (rest : List (Fin n)) (t : ℝ) :
    pandora_threshold_policy (b :: rest) t =
      .openBox b (fun v => if t < v then .stop else pandora_threshold_policy rest t) := rfl
