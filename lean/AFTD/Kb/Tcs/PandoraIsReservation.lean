import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS

/-!
# pandora_is_reservation

Topic: online_algorithms   Node: 164fc1a51ea9

Provenance: formalization of a published result. Source: arXiv:2610.13775 Section 3, Section 3.1 (reservation values of Weitzman's rule)

r is a vector of reservation values: for every box i, the expected excess E[(v_i - r_i)^+] of its value over r_i equals its opening cost c_i.
-/

/-- `r` is a vector of reservation values: `E[(v_i - r_i)^+] = c_i` for every box. -/
def pandora_is_reservation (inst : PandoraDeadlineInstance) (r : Fin inst.n → ℝ) : Prop :=
  ∀ i, ∑ v ∈ (inst.dist i).support, (inst.dist i).prob v * max (v - r i) 0 = inst.cost i
