import AFTD.Prelude
import AFTD.Kb.Tcs.RandomGreedySurvivalPoly

/-!
# random_greedy_survival_prob

Topic: online_algorithms   Node: 3199de4c6de7

Provenance: formalization of a published result. Source: arXiv:2611.13571 Lemma 3.1

For a finite simple graph J on a finite vertex type V with decidable equality and decidable adjacency, a vertex subset A : Finset V, and time t : ℝ, the survival probability P(J, A, t) obtained by evaluating the formal polynomial random_greedy_survival_poly J A at 1 - t.
-/

/-- The survival probability of vertex set A at time t in random greedy matching. -/
noncomputable def random_greedy_survival_prob {V : Type*} [Fintype V] [DecidableEq V]
    (J : SimpleGraph V) [DecidableRel J.Adj] (A : Finset V) (t : ℝ) : ℝ :=
  (random_greedy_survival_poly J A).eval (1 - t)
