import AFTD.Prelude
import AFTD.Kb.Tcs.IsMoorePenroseInverse
import AFTD.Kb.Tcs.PositiveMatrixOrderFourLeftStationary

/-!
# is_moore_penrose_inverse_zero

Topic: graphs   Node: aa089204c654

Provenance: helper lemma. folklore

For any natural number $n$, the $n \times n$ real zero matrix is its own Moore–Penrose pseudoinverse.
-/

/-- The zero matrix is its own Moore-Penrose pseudoinverse. -/
theorem is_moore_penrose_inverse_zero (n : ℕ) :
    is_moore_penrose_inverse (0 : Matrix (Fin n) (Fin n) ℝ) 0 := by first | exact positive_matrix_order_four_left_stationary | (apply positive_matrix_order_four_left_stationary <;> assumption) | (apply positive_matrix_order_four_left_stationary <;> simp_all) | simpa using positive_matrix_order_four_left_stationary | (simp only [is_moore_penrose_inverse] at *; first | exact positive_matrix_order_four_left_stationary | (apply positive_matrix_order_four_left_stationary <;> assumption) | (apply positive_matrix_order_four_left_stationary <;> simp_all) | simpa using positive_matrix_order_four_left_stationary)
