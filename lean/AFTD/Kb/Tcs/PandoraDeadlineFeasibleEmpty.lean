import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraThresholdPolicy
import AFTD.Kb.Tcs.PandoraDeadlineFeasible
import AFTD.Kb.Tcs.PandoraDeadlineInstance

/-!
# pandora_deadline_feasible_empty

Topic: online_algorithms   Node: 7abec74c98b5

Provenance: helper lemma. Sanity lemma for the definitions of arXiv:2610.13775 Section 3

Sanity: the empty set of boxes is deadline-feasible.
-/

theorem pandora_deadline_feasible_empty (inst : PandoraDeadlineInstance) :
    pandora_deadline_feasible inst ∅ := by
  intro j; simp
