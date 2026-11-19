import AFTD.Prelude
import AFTD.Kb.Tcs.ExplicitGramFactor432

/-!
# explicit_gram_matrix_32

Topic: combinatorics   Node: 3db549031567

Provenance: formalization of a published result. Source: arXiv:2611.23269, Section 2

The 32-by-32 integer Gram matrix explicit_gram_matrix_32 defined by explicit_gram_factor_4_32.transpose * explicit_gram_factor_4_32.
-/

/-- The 32x32 integer Gram matrix A = V.transpose * V. -/
def explicit_gram_matrix_32 : Matrix (Fin 32) (Fin 32) ℤ := explicit_gram_factor_4_32.transpose * explicit_gram_factor_4_32
