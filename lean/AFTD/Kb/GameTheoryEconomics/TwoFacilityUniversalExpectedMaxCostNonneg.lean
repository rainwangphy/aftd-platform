import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityUniversalExpectedMaxCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCostNonneg
import AFTD.Kb.GameTheoryEconomics.TwoFacilityUniversalMechanism
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCost

/-!
# two_facility_universal_expected_max_cost_nonneg

Topic: mechanism_design   Node: 4aeac319f521

Provenance: helper lemma. folklore

For any universally strategyproof two-facility mechanism M with finite nonempty index type K on a finite nonempty agent set ι in a metric space X and any position profile x : ι → X, two_facility_universal_expected_max_cost M x is nonnegative (0 ≤ two_facility_universal_expected_max_cost M x).
-/

/-- The expected max cost of a universally strategyproof two-facility mechanism is nonnegative. -/
theorem two_facility_universal_expected_max_cost_nonneg
    {ι X K : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι] [MetricSpace X] [Fintype K] [Nonempty K]
    {C : Finset X} {p : ι → Fin 2 → Bool}
    (M : TwoFacilityUniversalMechanism C p K) (x : ι → X) :
    0 ≤ two_facility_universal_expected_max_cost M x := by
  unfold two_facility_universal_expected_max_cost
  exact Finset.sum_nonneg fun k _ =>
    mul_nonneg (M.weights_mem.1 k) (two_facility_max_cost_nonneg x p (M.mech k x))
