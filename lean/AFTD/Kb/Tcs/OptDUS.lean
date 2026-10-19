import AFTD.Prelude
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# optDUS

Topic: online_algorithms   Node: 06886a70c316

Provenance: formalization of a published result. Source: arXiv:2610.13775 Sec. 2.1

The optimal expected net utility `optDUS inst` under deferred-until-stopping commitment for a Pandora's problem instance with deadlines `inst : PandoraDeadlineInstance`, defined as the supremum of `expectedUtilityDUS inst π` over all valid adaptive policies `π : AdaptivePolicy inst.n` satisfying `IsValidPolicy inst π`.
-/

/-- Optimal expected net utility over all valid adaptive policies under deferred-until-stopping commitment (benchmark OPT). -/
noncomputable def optDUS (inst : PandoraDeadlineInstance) : ℝ := ⨆ (π : AdaptivePolicy inst.n) (_ : IsValidPolicy inst π), expectedUtilityDUS inst π
