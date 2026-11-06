import AFTD.Prelude
import AFTD.Kb.Optimization.SubmodQueryTree

/-!
# RandomizedSubmodTester

Topic: submodular   Node: 1a5ff7fba391

Provenance: formalization of a published result. Source: arXiv:2611.02374, Def. 2.5

A randomized tester making at most q queries, modeled as a finite probability distribution over deterministic decision trees of depth at most q.
-/

/-- A randomized tester of query complexity q, given by a probability distribution over decision trees of depth q. -/
structure RandomizedSubmodTester (n k q : ℕ) where
  m : ℕ
  prob : Fin m → ℝ
  prob_nonneg : ∀ i, 0 ≤ prob i
  prob_sum : ∑ i, prob i = 1
  tree : Fin m → SubmodQueryTree n k q
