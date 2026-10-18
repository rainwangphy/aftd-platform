import AFTD.Prelude

/-!
# two_facility_cost

Topic: mechanism_design   Node: dbef6e3f3264

Provenance: formalization of a published result. Source: arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces), Sec. 2, individual cost

cost_i(c) = sum over j in {F_1, F_2} of p_ij * d(x_i, c_j).
-/

/-- Individual cost of agent `i` at position `x i` with approval preferences `p i : Fin 2 → Bool` when facility `j` is placed at `c j`: the total distance to the approved facilities. -/
noncomputable def two_facility_cost {ι X : Type*} [MetricSpace X] (x : ι → X) (p : ι → Fin 2 → Bool)
    (i : ι) (c : Fin 2 → X) : ℝ :=
  ∑ j, if p i j then dist (x i) (c j) else 0
