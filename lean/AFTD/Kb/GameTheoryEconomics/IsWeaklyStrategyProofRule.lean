import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PairwiseDominates

/-!
# is_weakly_strategy_proof_rule

Topic: fair_division   Node: 4eac47e47781

Provenance: formalization of a published result. Source: arXiv:2611.09685 Section 5 (p. 14)

A social choice rule f is weakly strategy-proof if for every preference profile succ, every agent i, and every alternative linear order succ'_i, the bundle f (Function.update succ i succ'_i) i that agent i receives under the unilateral misreport does not strictly pairwise-dominate i's truthful bundle f succ i under i's true preference order.
-/

/-- A social choice rule is weakly strategy-proof if no agent can strictly improve her bundle under pairwise dominance by unilaterally misreporting her preference order. -/
def is_weakly_strategy_proof_rule {Agent Object : Type*} [DecidableEq Agent] (f : (Agent → LinearOrder Object) → Agent → Finset Object) : Prop := ∀ (succ : Agent → LinearOrder Object) (i : Agent) (succ'_i : LinearOrder Object), ¬ (pairwise_dominates (succ i).le (f (Function.update succ i succ'_i) i) (f succ i) ∧ ¬ pairwise_dominates (succ i).le (f succ i) (f (Function.update succ i succ'_i) i))
