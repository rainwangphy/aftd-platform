import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityUniversalMechanism
import AFTD.Kb.GameTheoryEconomics.TwoFacilityMaxCost

/-!
# two_facility_universal_expected_max_cost

Topic: mechanism_design   Node: 8686f2ccdaa7

Provenance: formalization of a published result. Source: scout/2610-18006-truthful-two-facility-location-with-candidate-locations-in.md:202

Given types ι, X, and K with DecidableEq ι, Fintype ι, Nonempty ι, MetricSpace X, Fintype K, and Nonempty K, a candidate set C : Finset X, a preference profile p : ι → Fin 2 → Bool, a universally strategyproof mechanism M : TwoFacilityUniversalMechanism C p K, and an agent position profile x : ι → X, two_facility_universal_expected_max_cost M x is the sum over k : K of M.weights k * two_facility_max_cost x p (M.mech k x).
-/

/-- The expected max cost of a universally strategyproof mechanism on an agent position profile x. -/
noncomputable def two_facility_universal_expected_max_cost
    {ι X K : Type*} [DecidableEq ι] [Fintype ι] [Nonempty ι] [MetricSpace X] [Fintype K] [Nonempty K]
    {C : Finset X} {p : ι → Fin 2 → Bool}
    (M : TwoFacilityUniversalMechanism C p K) (x : ι → X) : ℝ := ∑ k : K, M.weights k * two_facility_max_cost x p (M.mech k x)
