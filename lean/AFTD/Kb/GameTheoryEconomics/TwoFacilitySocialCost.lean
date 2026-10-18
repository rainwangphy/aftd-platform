import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost

/-!
# two_facility_social_cost

Topic: mechanism_design   Node: 1cb1c4708206

Provenance: formalization of a published result. Source: arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces), Sec. 2, social cost

SC(c) = sum over agents i of cost_i(c).
-/

/-- Social cost: the sum of the individual costs. -/
noncomputable def two_facility_social_cost {ι X : Type*} [Fintype ι] [MetricSpace X] (x : ι → X)
    (p : ι → Fin 2 → Bool) (c : Fin 2 → X) : ℝ :=
  ∑ i, two_facility_cost x p i c
