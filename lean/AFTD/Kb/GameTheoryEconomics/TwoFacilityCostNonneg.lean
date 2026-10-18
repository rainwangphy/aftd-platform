import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost

/-!
# two_facility_cost_nonneg

Topic: mechanism_design   Node: d578457fbbc1

Provenance: helper lemma. sanity lemma for two_facility_cost (arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces))

Sanity: every individual cost is nonnegative.
-/

theorem two_facility_cost_nonneg {ι X : Type*} [MetricSpace X] (x : ι → X) (p : ι → Fin 2 → Bool)
    (i : ι) (c : Fin 2 → X) : 0 ≤ two_facility_cost x p i c := by
  unfold two_facility_cost
  apply Finset.sum_nonneg
  intro j hj
  split_ifs with hp
  · exact dist_nonneg
  · exact le_refl 0
