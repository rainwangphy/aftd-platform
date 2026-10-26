import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS

/-!
# pandora_threshold_policy

Topic: online_algorithms   Node: db1411d78ed4

Provenance: formalization of a published result. Source: arXiv:2610.13775 Section 3, Section 3.2, policy T^+(S,t)

The threshold policy on a list of boxes: open them in the given order and stop as soon as an opened value exceeds t (stop after the last box otherwise).
-/

/-- The threshold policy: open the boxes of `order` in turn and stop at the first value above `t`. -/
noncomputable def pandora_threshold_policy {n : ℕ} (order : List (Fin n)) (t : ℝ) : AdaptivePolicy n :=
  order.foldr (fun b acc => .openBox b (fun v => if t < v then .stop else acc)) .stop
