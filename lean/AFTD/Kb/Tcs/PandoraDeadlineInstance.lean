import AFTD.Prelude
import AFTD.Kb.Tcs.DiscreteDist

/-!
# PandoraDeadlineInstance

Topic: online_algorithms   Node: b75c5c742031

Provenance: formalization of a published result. Source: arXiv:2610.13775, Sec. 2.1

An instance of Pandora's problem with deadlines consisting of n boxes, each with a non-negative opening cost, a positive integer deadline, and an independent discrete value distribution.
-/

/-- An instance of Pandora's problem with deadlines. -/
structure PandoraDeadlineInstance where
  n : ℕ
  cost : Fin n → ℝ
  deadline : Fin n → ℕ
  dist : Fin n → DiscreteDist
  cost_nonneg : ∀ i, 0 ≤ cost i
  deadline_pos : ∀ i, 1 ≤ deadline i
