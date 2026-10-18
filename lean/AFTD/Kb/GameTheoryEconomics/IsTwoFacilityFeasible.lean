import AFTD.Prelude

/-!
# IsTwoFacilityFeasible

Topic: mechanism_design   Node: 6ae434b97274

Provenance: formalization of a published result. Source: arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces), Sec. 2, feasible solution

c = (c_1, c_2) is feasible iff c_1, c_2 ∈ C and c_1 ≠ c_2.
-/

/-- A feasible solution: the two facilities at two distinct candidate locations. -/
def IsTwoFacilityFeasible {X : Type*} (C : Finset X) (c : Fin 2 → X) : Prop :=
  c 0 ∈ C ∧ c 1 ∈ C ∧ c 0 ≠ c 1
