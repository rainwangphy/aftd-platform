import AFTD.Prelude
import AFTD.Kb.Optimization.CubeFunc
import AFTD.Kb.Optimization.RandomizedSubmodTester
import AFTD.Kb.Optimization.SubmodQueryTreeEval

/-!
# randomized_submod_tester_accept_prob

Topic: submodular   Node: e96fde8c0776

Provenance: formalization of a published result. Source: arXiv:2611.02374, Def. 2.5

The probability that a randomized tester accepts an input function f, given by the expected acceptance over its decision trees.
-/

/-- Acceptance probability of a randomized tester on an input function. -/
noncomputable def randomized_submod_tester_accept_prob {n k q : ℕ}
    (A : RandomizedSubmodTester n k q) (f : CubeFunc n k) : ℝ := ∑ i, if submod_query_tree_eval (A.tree i) f then A.prob i else 0
