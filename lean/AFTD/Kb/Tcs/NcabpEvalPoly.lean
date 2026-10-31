import AFTD.Prelude
import AFTD.Kb.Tcs.AffineForm
import AFTD.Kb.Tcs.AffineFormToFreeAlgebra
import AFTD.Kb.Tcs.NcABP
import AFTD.Kb.Tcs.NcabpMatrix

/-!
# ncabp_eval_poly

Topic: algebraic_complexity   Node: 2d7702e1e54b

Provenance: formalization of a published result. Source: arXiv:2610.37677, Section 1.1 and Section 3.2

Given a commutative semiring F, parameters m, S : ℕ, and an ncABP A : NcABP F m S, ncabp_eval_poly A is the polynomial in FreeAlgebra F (Fin m) defined as the (A.source, A.sink) entry of the sum ∑ k ∈ Finset.range (S + 1), (ncabp_matrix A) ^ k.
-/

/-- The noncommutative polynomial in FreeAlgebra F (Fin m) computed by an ncABP. -/
def ncabp_eval_poly {F : Type*} [CommSemiring F] {m S : ℕ} (A : NcABP F m S) :
    FreeAlgebra F (Fin m) := open BigOperators in (∑ k ∈ Finset.range (S + 1), (ncabp_matrix A ^ k)) A.source A.sink
