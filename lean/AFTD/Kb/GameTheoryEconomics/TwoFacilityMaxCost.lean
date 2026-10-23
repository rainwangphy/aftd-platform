import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TwoFacilityCost

/-!
# two_facility_max_cost

Topic: mechanism_design   Node: c7778ffa02c1

Provenance: formalization of a published result. Source: scout/2610-18006-truthful-two-facility-location-with-candidate-locations-in.md:188

Given a finite and nonempty set of agents ι, a metric space X, agent positions x, approval preferences p, and facility locations c, the max cost of c is the finite maximum over all agents i ∈ ι of two_facility_cost x p i c.
-/

/-- The maximum individual cost among all agents for a two-facility solution c. -/
noncomputable def two_facility_max_cost {ι X : Type*} [Fintype ι] [Nonempty ι] [MetricSpace X]
    (x : ι → X) (p : ι → Fin 2 → Bool) (c : Fin 2 → X) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => two_facility_cost x p i c)
