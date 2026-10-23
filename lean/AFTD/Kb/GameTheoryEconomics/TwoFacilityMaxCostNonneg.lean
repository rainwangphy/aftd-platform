import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCostNonneg
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCostLeMaxCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost

/-!
# two_facility_max_cost_nonneg

Topic: mechanism_design   Node: d00dd74bd314

Provenance: helper lemma. folklore

For a finite nonempty set of agents, the max cost of any two-facility solution is nonnegative.
-/

/-- The max cost of any two-facility solution is nonnegative. -/
theorem two_facility_max_cost_nonneg {ι X : Type*} [Fintype ι] [Nonempty ι] [MetricSpace X]
    (x : ι → X) (p : ι → Fin 2 → Bool) (c : Fin 2 → X) :
    0 ≤ two_facility_max_cost x p c := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact le_trans (two_facility_cost_nonneg x p i c) (two_facility_cost_le_max_cost x p i c)
