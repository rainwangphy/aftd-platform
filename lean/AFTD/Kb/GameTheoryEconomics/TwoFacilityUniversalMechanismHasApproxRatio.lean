import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityUniversalMechanism
import AFTD.Kb.GameTheoryEconomics.TwoFacilityUniversalExpectedMaxCost
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCost
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible

/-!
# TwoFacilityUniversalMechanismHasApproxRatio

Topic: mechanism_design   Node: 2953427656be

Provenance: formalization of a published result. Source: scout/2610-18006-truthful-two-facility-location-with-candidate-locations-in.md:194

Given types ι, X, and K with DecidableEq ι, Fintype ι, Nonempty ι, MetricSpace X, Fintype K, and Nonempty K, candidate set C : Finset X, preference profile p : ι → Fin 2 → Bool, a universally strategyproof mechanism M : TwoFacilityUniversalMechanism C p K, and a real number α, TwoFacilityUniversalMechanismHasApproxRatio M α asserts that for every position profile x : ι → X and every feasible solution o : Fin 2 → X (satisfying IsTwoFacilityFeasible C o), two_facility_universal_expected_max_cost M x ≤ α * two_facility_max_cost x p o.
-/

/-- A universally strategyproof mechanism has approximation ratio at most α for max cost if its expected max cost is at most α times the optimal max cost on every profile. -/
def TwoFacilityUniversalMechanismHasApproxRatio
    {ι X K : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι] [MetricSpace X] [Fintype K] [Nonempty K]
    {C : Finset X} {p : ι → Fin 2 → Bool}
    (M : TwoFacilityUniversalMechanism C p K) (α : ℝ) : Prop := ∀ (x : ι → X) (o : Fin 2 → X), IsTwoFacilityFeasible C o →
    two_facility_universal_expected_max_cost M x ≤ α * two_facility_max_cost x p o
