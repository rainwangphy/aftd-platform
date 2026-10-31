import AFTD.Prelude

/-!
# fiber_sum_vec

Topic: submodular   Node: 7038338f82bd

Provenance: formalization of a published result. Source: arXiv:2610.35433

Given an assignment of n microstates to m energy levels, the fiber sum vector of a microstate distribution y has k-th component equal to the sum of y_i over all microstates i assigned to level k.
-/

/-- The fiber sum vector aggregates microstate populations over the fibers of an energy-level assignment. -/
def fiber_sum_vec {n m : ℕ} (proj : Fin n → Fin m) (y : Fin n → ℝ) : Fin m → ℝ := fun k => ∑ i ∈ Finset.univ.filter (fun i => proj i = k), y i
