import AFTD.Prelude
import AFTD.Kb.Tcs.PMState
import AFTD.Kb.Tcs.PMStateStep

/-!
# pm_step_facts

Topic: algorithms   Node: 2536310b4b91

The adversary only appends the query and its answer to the list of facts.
-/

/-- The adversary only appends the query and its answer to the list of facts. -/
theorem pm_step_facts {n : ℕ} (S : PMState n) (a b : Fin n) :
    (S.step a b).2.facts = (a, b, (S.step a b).1) :: S.facts := by
  unfold PMState.step
  split_ifs <;> rfl
