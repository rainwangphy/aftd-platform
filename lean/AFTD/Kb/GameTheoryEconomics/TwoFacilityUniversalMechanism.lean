import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityStrategyproof
import AFTD.Kb.GameTheoryEconomics.IsTwoFacilityFeasible

/-!
# TwoFacilityUniversalMechanism

Topic: mechanism_design   Node: 628069247f3f

Provenance: formalization of a published result. Source: scout/2610-18006-truthful-two-facility-location-with-candidate-locations-in.md:202

Given types ι and X with DecidableEq ι and MetricSpace X, a finite set C : Finset X of candidate locations, an approval preference profile p : ι → Fin 2 → Bool, and a finite nonempty index type K with Fintype K and Nonempty K, a universally strategyproof mechanism TwoFacilityUniversalMechanism C p K consists of a weight function weights : K → ℝ satisfying weights ∈ stdSimplex ℝ K, and a family of deterministic mechanisms mech : K → (ι → X) → Fin 2 → X such that for every k : K and profile x : ι → X, mech k x is feasible in C (IsTwoFacilityFeasible C (mech k x)), and for every k : K, mech k is strategyproof with respect to p (IsTwoFacilityStrategyproof p (mech k)).
-/

/-- A universally strategyproof mechanism parameterized by a finite index type K is a convex combination of deterministic strategyproof mechanisms. -/
structure TwoFacilityUniversalMechanism {ι X : Type*} [DecidableEq ι] [MetricSpace X]
    (C : Finset X) (p : ι → Fin 2 → Bool) (K : Type*) [Fintype K] [Nonempty K] where
  weights : K → ℝ
  weights_mem : weights ∈ stdSimplex ℝ K
  mech : K → (ι → X) → (Fin 2 → X)
  feasible : ∀ k x, IsTwoFacilityFeasible C (mech k x)
  strategyproof : ∀ k, IsTwoFacilityStrategyproof p (mech k)
