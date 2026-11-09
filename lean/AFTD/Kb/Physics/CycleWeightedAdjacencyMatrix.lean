import AFTD.Prelude

/-!
# cycle_weighted_adjacency_matrix

Topic: quantum_mechanics   Node: d0ae678c87b3

Provenance: formalization of a published result. Source: arXiv:2610.27080, Section III.1 and Eq. (8)

For a type α equipped with AddZeroClass, a natural number n, and a function t : Fin n → α, cycle_weighted_adjacency_matrix n t is the Fin n × Fin n matrix over α whose (i, j)-entry is t i + t j if (SimpleGraph.cycleGraph n).Adj i j, and 0 otherwise.
-/

/-- The weighted adjacency matrix of the cycle graph C_n with edge weights given by sums of endpoint values. -/
def cycle_weighted_adjacency_matrix {α : Type*} [AddZeroClass α] (n : ℕ) (t : Fin n → α) :
    Matrix (Fin n) (Fin n) α := Matrix.of fun i j => if (SimpleGraph.cycleGraph n).Adj i j then t i + t j else 0
