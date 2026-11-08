import AFTD.Prelude

/-!
# MultidimInstance

Topic: online_algorithms   Node: 2aee41886c2a

Provenance: formalization of a published result. Source: arXiv:2611.07905 Tight Worst-Case Completion-Time Bounds for Dominant Resource Fairness, Section 2.1

An instance of multidimensional scheduling with D resource types and zero release times, consisting of a positive number of jobs n with processing requirements p_j > 0, rate caps u_j > 0, and demand vectors a_j in [0, 1]^D such that each entry is in [0, 1] and at least one entry equals 1.
-/

/-- An instance of multidimensional scheduling with D resources and zero release times. -/
structure MultidimInstance (D : ℕ) where
  n : ℕ
  hn : 0 < n
  p : Fin n → ℝ
  hp : ∀ j, 0 < p j
  u : Fin n → ℝ
  hu : ∀ j, 0 < u j
  a : Fin n → Fin D → ℝ
  ha_nonneg : ∀ j d, 0 ≤ a j d
  ha_le_one : ∀ j d, a j d ≤ 1
  ha_dominant : ∀ j, ∃ d, a j d = 1
