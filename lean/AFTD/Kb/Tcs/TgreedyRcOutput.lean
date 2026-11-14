import AFTD.Prelude
import AFTD.Kb.Tcs.MgreedyRcStep
import AFTD.Kb.Tcs.GreedyRcStep

/-!
# tgreedy_rc_output

Topic: approximation   Node: e49974b95e91

Provenance: formalization of a published result. Source: arXiv:2611.16573, Algorithm 3

For cm : Γ → Γ, S : Finset (List Γ) and t : List Γ, tgreedy_rc_output cm S t holds when there is T : Finset (List Γ) such that the state (S, ∅) reaches (∅, T) by zero or more mgreedy_rc_step cm steps (Relation.ReflTransGen), and T reaches the singleton {t} by zero or more greedy_rc_step cm steps: t is an output of an execution of TGREEDY-RC.
-/

/-- t is the output of some execution of TGREEDY-RC (Algorithm 3) on S: MGREEDY-RC run from (S, ∅) until S is empty gives T (without the final concatenation), and GREEDY-RC run on T leaves the single string t. -/
def tgreedy_rc_output {Γ : Type*} [DecidableEq Γ] (cm : Γ → Γ)
    (S : Finset (List Γ)) (t : List Γ) : Prop :=
  ∃ T : Finset (List Γ),
    Relation.ReflTransGen (mgreedy_rc_step cm) (S, ∅) (∅, T) ∧
    Relation.ReflTransGen (greedy_rc_step cm) T {t}
