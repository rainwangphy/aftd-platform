import AFTD.Prelude
import AFTD.Kb.Tcs.ExpectedUtilityDTD
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# optDTD

Topic: online_algorithms   Node: 7d01282ee526

Provenance: formalization of a published result. Source: arXiv:2610.13775 Sec. 2.1

The optimal expected net utility `optDTD inst` under deferred-to-deadline commitment for a Pandora's problem instance with deadlines `inst : PandoraDeadlineInstance`, defined as the supremum of `expectedUtilityDTD inst π` over all valid adaptive policies `π : AdaptivePolicy inst.n` satisfying `IsValidPolicy inst π`.
-/

/-- Optimal expected net utility over all valid adaptive policies under deferred-to-deadline commitment. -/
noncomputable def optDTD (inst : PandoraDeadlineInstance) : ℝ := ⨆ (π : AdaptivePolicy inst.n) (_ : IsValidPolicy inst π), expectedUtilityDTD inst π
