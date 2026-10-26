import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS

/-!
# pandora_deadline_feasible

Topic: online_algorithms   Node: 76e1079f78dc

Provenance: formalization of a published result. Source: arXiv:2610.13775 Section 3, Section 3.1 and Lemma 2 (feasibility test)

A set S of boxes is deadline-feasible if for every j at most j of its boxes have deadline at most j (equivalently, by Lemma 2, its boxes can be opened one per round by their deadlines).
-/

/-- A set of boxes is deadline-feasible: for every `j`, at most `j` of its boxes have deadline `≤ j`. -/
def pandora_deadline_feasible (inst : PandoraDeadlineInstance) (S : Finset (Fin inst.n)) : Prop :=
  ∀ j : ℕ, (S.filter (fun i => inst.deadline i ≤ j)).card ≤ j
