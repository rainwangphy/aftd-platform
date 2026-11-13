import AFTD.Prelude
import AFTD.Kb.Optimization.MatrixHasPsdFactorizationOfNonneg

/-!
# matrix_trace_unitaryGroup_one

Topic: quantum   Node: 07f2de129693

Provenance: helper lemma. step towards local_encoding_via_abelian_traceless_group

The trace of the identity unitary matrix indexed by a finite type n equals the cardinality of n.
-/

/-- The trace of the identity matrix is the dimension. -/
theorem matrix_trace_unitaryGroup_one {n : Type*} [Fintype n] [DecidableEq n] :
    Matrix.trace (((1 : Matrix.unitaryGroup n ℂ)) : Matrix n n ℂ) = (Fintype.card n : ℂ) := by first | exact matrix_has_psd_factorization_of_nonneg | (apply matrix_has_psd_factorization_of_nonneg <;> assumption) | (apply matrix_has_psd_factorization_of_nonneg <;> simp_all) | simpa using matrix_has_psd_factorization_of_nonneg
