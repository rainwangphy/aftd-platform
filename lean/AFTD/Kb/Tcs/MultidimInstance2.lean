import AFTD.Prelude

/-!
# MultidimInstance2

Topic: online_algorithms   Node: 1b44636315b2

Provenance: formalization of a published result. Source: arXiv:2611.07905 Sec. 2.1

An instance of multidimensional scheduling with 2 resource types and zero release times, consisting of a positive number of jobs n with processing requirements p_j > 0, rate caps u_j > 0, and demand vectors a_j in [0, 1]^2 normalized so max(a_j 0, a_j 1) = 1.
-/

/-- A multidimensional scheduling instance with D=2 resources and zero release times. -/
structure MultidimInstance2 where
  n : ℕ
  hn : 0 < n
  p : Fin n → ℝ
  hp : ∀ j, 0 < p j
  u : Fin n → ℝ
  hu : ∀ j, 0 < u j
  a : Fin n → Fin 2 → ℝ
  ha_nonneg : ∀ j d, 0 ≤ a j d
  ha_le_one : ∀ j d, a j d ≤ 1
  ha_dominant : ∀ j, max (a j 0) (a j 1) = 1
