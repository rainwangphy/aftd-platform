import AFTD.Prelude
import AFTD.Kb.Tcs.IsDistanceRegularWith

/-!
# is_realizable_intersection_array

Topic: graphs   Node: cdfac680b41d

Provenance: formalization of a published result. Source: arXiv:2611.05762, Sec. 3.1 & Problem 9.2.1

An intersection array (b, c) with b, c : Fin d → ℕ of diameter d is realizable if there exists a finite nonempty vertex type V and a simple graph G on V such that is_distance_regular_with G d b c holds.
-/

/-- An intersection array is realizable if there exists a finite nonempty distance-regular graph with that intersection array. -/
def is_realizable_intersection_array (d : ℕ) (b c : Fin d → ℕ) : Prop := ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V), ∃ (G : SimpleGraph V), is_distance_regular_with G d b c
