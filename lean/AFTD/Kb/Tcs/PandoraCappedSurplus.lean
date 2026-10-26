import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS

/-!
# pandora_capped_surplus

Topic: online_algorithms   Node: abe5fd13dbd8

Provenance: formalization of a published result. Source: arXiv:2610.13775 Section 3, Section 3.1, definition of w_i(t)

The reservation-capped threshold surplus of box i at threshold t: w_i(t) = E[(min(v_i, r_i) - t)^+].
-/

/-- Reservation-capped threshold surplus `w_i(t) = E[(min(v_i, r_i) - t)^+]`. -/
noncomputable def pandora_capped_surplus (inst : PandoraDeadlineInstance) (r : Fin inst.n → ℝ)
    (i : Fin inst.n) (t : ℝ) : ℝ :=
  ∑ v ∈ (inst.dist i).support, (inst.dist i).prob v * max (min v (r i) - t) 0
