import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RandomizedOnlineChoreAlgorithm
import AFTD.Kb.GameTheoryEconomics.DeterministicOnlineChoreRule

/-!
# deterministic_to_randomized

Topic: fair_division   Node: a39b35747089

Provenance: formalization of a published result. Source: arXiv:2611.00432 Sec 4

Lifts a deterministic prediction-free online chore rule rule : DeterministicOnlineChoreRule n to a randomized online chore algorithm deterministic_to_randomized rule : RandomizedOnlineChoreAlgorithm n with sample space Unit, probability mass function PMF.pure (), and constant rule function fun _ => rule.
-/

/-- Lift a deterministic online chore rule to a randomized online chore algorithm. -/
noncomputable def deterministic_to_randomized {n : ℕ} (rule : DeterministicOnlineChoreRule n) :
    RandomizedOnlineChoreAlgorithm n :=
  ⟨Unit, PMF.pure (), fun _ => rule⟩
