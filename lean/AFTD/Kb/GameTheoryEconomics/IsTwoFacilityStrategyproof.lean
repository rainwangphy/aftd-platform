import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost

/-!
# IsTwoFacilityStrategyproof

Topic: mechanism_design   Node: ef8e48d286a2

Provenance: formalization of a published result. Source: scout/2610-18006-truthful-two-facility-location-with-candidate-locations-in.md:197

In the two-facility location problem on a metric space X with agent set ι and approval preferences p, a deterministic mechanism M : (ι → X) → (Fin 2 → X) is strategyproof if for every position profile x : ι → X, every agent i : ι, and every misreport x' : X, the cost of agent i under M x is at most the cost of agent i under M applied to the profile where agent i's position is updated to x'.
-/

/-- A deterministic two-facility mechanism is strategyproof if no agent can reduce her cost by misreporting her position. -/
def IsTwoFacilityStrategyproof {ι X : Type*} [DecidableEq ι] [MetricSpace X]
    (p : ι → Fin 2 → Bool) (M : (ι → X) → (Fin 2 → X)) : Prop := ∀ (x : ι → X) (i : ι) (x' : X),
    two_facility_cost x p i (M x) ≤ two_facility_cost x p i (M (Function.update x i x'))
