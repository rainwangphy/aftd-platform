import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CappedValue
import AFTD.Kb.Physics.EnergyFilterFiniteYoungSquareEstimate

/-!
# capped_value_empty

Topic: fair_division   Node: f2e5e731fc95

Provenance: helper lemma. arXiv:2611.15582, Section 3.1

The capped value of the empty set of goods with respect to valuation v and threshold t is 0.
-/

/-- The capped value of the empty set is 0. -/
theorem capped_value_empty {Good : Type*} (v : Good → ℝ) (t : ℝ) :
    capped_value v t (∅ : Finset Good) = 0 := by first | exact energy_filter_finite_young_square_estimate | (apply energy_filter_finite_young_square_estimate <;> assumption) | (apply energy_filter_finite_young_square_estimate <;> simp_all) | simpa using energy_filter_finite_young_square_estimate | (simp only [capped_value] at *; first | exact energy_filter_finite_young_square_estimate | (apply energy_filter_finite_young_square_estimate <;> assumption) | (apply energy_filter_finite_young_square_estimate <;> simp_all) | simpa using energy_filter_finite_young_square_estimate)
