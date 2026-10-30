import AFTD.Prelude
import AFTD.Kb.NumberTheory.RecurrenceBMap
import AFTD.Kb.NumberTheory.RecurrenceBMapBijective
import AFTD.Kb.NumberTheory.RecurrenceBMapOrbitPeriodic
import AFTD.Kb.NumberTheory.RecurrenceBMapFixedPointUnique

/-!
# recurrence_b_transition_bijective_and_orbit_periodic_and_unique_fixed_point

Topic: elementary_number_theory   Node: 5346fd7604cb

Provenance: formalization of a published result. Source: arXiv:2610.34300 Proposition 7

For any integer k ≥ 2, the transition map of recurrence (B) on (ℤ/3ℤ)^k is bijective, every orbit is purely periodic (for every state w, there exists m > 0 such that the m-th iterate of the map on w is w), and the zero state is the unique fixed point of the map.
-/

/-- Proposition 7: Bijectivity, pure periodicity, and unique fixed point of recurrence B state map. -/
theorem recurrence_b_transition_bijective_and_orbit_periodic_and_unique_fixed_point (k : ℕ) (hk : 2 ≤ k) : Function.Bijective (recurrence_b_map k) ∧ (∀ w : Fin k → ZMod 3, ∃ m > 0, (recurrence_b_map k)^[m] w = w) ∧ (∀ w : Fin k → ZMod 3, recurrence_b_map k w = w ↔ w = 0) := ⟨recurrence_b_map_bijective k hk, recurrence_b_map_orbit_periodic k hk, recurrence_b_map_fixed_point_unique k hk⟩
