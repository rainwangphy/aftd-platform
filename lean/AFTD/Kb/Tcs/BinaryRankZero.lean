import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryRank
import AFTD.Kb.Tcs.PositiveMatrixOrderFourLeftStationary

/-!
# binary_rank_zero

Topic: streaming   Node: 89bb36dc8d2a

Provenance: formalization of a published result. Source: arXiv:2611.14163, Definition 2.1

The all-zero binary matrix of dimensions n × m with entries in Fin 2 has binary rank 0.
-/

/-- The all-zero binary matrix has binary rank zero. -/
theorem binary_rank_zero (n m : ℕ) :
    binary_rank (0 : Matrix (Fin n) (Fin m) (Fin 2)) = 0 := by first | exact positive_matrix_order_four_left_stationary | (apply positive_matrix_order_four_left_stationary <;> assumption) | (apply positive_matrix_order_four_left_stationary <;> simp_all) | simpa using positive_matrix_order_four_left_stationary | (simp only [binary_rank] at *; first | exact positive_matrix_order_four_left_stationary | (apply positive_matrix_order_four_left_stationary <;> assumption) | (apply positive_matrix_order_four_left_stationary <;> simp_all) | simpa using positive_matrix_order_four_left_stationary)
