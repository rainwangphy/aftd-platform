import AFTD.Prelude
import AFTD.Kb.Tcs.TwoBoxDeadlineInst
import AFTD.Kb.Tcs.TwoBoxFairValueDist
import AFTD.Kb.Tcs.TwoBoxRiskyValueDist
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.DiscreteDist

/-!
# two_box_pi01_valid

Topic: online_algorithms   Node: 01dd26280c37

Provenance: helper lemma. step towards two_box_counterexample_family

The policy "open box 0, then box 1, then stop" is valid for the two-box instance.
-/

/-- Opening box 0 then box 1 is a valid policy for the two-box instance. -/
theorem two_box_pi01_valid (M : ℕ) (hM : 1 < M) :
    IsValidPolicy (two_box_deadline_inst M hM)
      (AdaptivePolicy.openBox (0 : Fin 2) (fun _ => AdaptivePolicy.openBox (1 : Fin 2) (fun _ => AdaptivePolicy.stop))) := by
  unfold IsValidPolicy
  refine ⟨by simp, ?_, ?_⟩
  · simp [two_box_deadline_inst]
  · intro v hv
    refine ⟨by simp, ?_, ?_⟩
    · simp [two_box_deadline_inst]
    · intro w hw
      trivial
