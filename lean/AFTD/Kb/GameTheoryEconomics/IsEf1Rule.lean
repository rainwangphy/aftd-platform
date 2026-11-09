import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PairwiseDominates

/-!
# is_ef1_rule

Topic: fair_division   Node: 91e6111cca4d

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 3 (p. 8)

Given types Agent and Object with decidable equality on Object, a rule f : (Agent → LinearOrder Object) → Agent → Finset Object satisfies is_ef1_rule if for every preference profile succ : Agent → LinearOrder Object and all agents i j : Agent, there exists a subset S of bundle f succ j with cardinality at most 1 such that bundle f succ i pairwise-dominates f succ j \ S under (succ i).le.
-/

/-- A social choice rule satisfies EF1 if at every preference profile, for any two agents i and j, agent i does not envy j's bundle after removing at most one object, under pairwise dominance. -/
def is_ef1_rule {Agent Object : Type*} [DecidableEq Object] (f : (Agent → LinearOrder Object) → Agent → Finset Object) : Prop := ∀ (succ : Agent → LinearOrder Object) (i j : Agent), ∃ S ⊆ f succ j, S.card ≤ 1 ∧ pairwise_dominates (succ i).le (f succ i) (f succ j \ S)
