import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasUpgradeRecourse

/-!
# DeterministicOnlineChoreRule

Topic: fair_division   Node: 5433b4114345

Provenance: formalization of a published result. Source: arXiv:2611.00432 Sec 2 & 4

A deterministic prediction-free online chore allocation algorithm for n agents with upgrade recourse: for each sequence of arrival costs c, it outputs a sequence of allocations A m such that A m depends only on the chore costs before step m, and for any nonnegative arrival costs c, the sequence of allocations has upgrade recourse.
-/

/-- A deterministic prediction-free online chore allocation algorithm with upgrade recourse for n agents. -/
structure DeterministicOnlineChoreRule (n : ℕ) where
  alloc : (Fin n → ℕ → ℝ) → (∀ m : ℕ, Fin m → Fin n)
  prediction_free : ∀ (m : ℕ) (c c' : Fin n → ℕ → ℝ),
    (∀ i, ∀ k < m, c i k = c' i k) → alloc c m = alloc c' m
  upgrade_recourse : ∀ (c : Fin n → ℕ → ℝ),
    (∀ i t, 0 ≤ c i t) → has_upgrade_recourse n c (alloc c)
