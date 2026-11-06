import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DeterministicOnlineChoreRule

/-!
# RandomizedOnlineChoreAlgorithm

Topic: fair_division   Node: e80cb08c9448

Provenance: formalization of a published result. Source: arXiv:2611.00432 Sec 2 & 4

A structure parameterized by the number of agents n : ℕ, consisting of three bundled fields: a sample space type Ω : Type, a probability mass function dist : PMF Ω, and a function rule : Ω → DeterministicOnlineChoreRule n assigning each sample to a deterministic decision rule.
-/

/-- A randomized prediction-free online chore allocation algorithm with upgrade recourse for n agents. -/
structure RandomizedOnlineChoreAlgorithm (n : ℕ) where
  Ω : Type
  dist : PMF Ω
  rule : Ω → DeterministicOnlineChoreRule n
