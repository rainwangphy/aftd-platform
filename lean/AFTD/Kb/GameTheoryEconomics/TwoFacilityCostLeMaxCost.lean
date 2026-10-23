import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCost

/-!
# two_facility_cost_le_max_cost

Topic: mechanism_design   Node: 5d065ea33aca

Provenance: helper lemma. folklore

For a finite nonempty set of agents, every agent i incurs individual cost under solution c that is at most the max cost of c.
-/

/-- Each agent's individual cost is at most the max cost of the solution. -/
theorem two_facility_cost_le_max_cost {ι X : Type*} [Fintype ι] [Nonempty ι] [MetricSpace X]
    (x : ι → X) (p : ι → Fin 2 → Bool) (i : ι) (c : Fin 2 → X) :
    two_facility_cost x p i c ≤ two_facility_max_cost x p c :=
  Finset.le_sup' (fun j => two_facility_cost x p j c) (Finset.mem_univ i)
