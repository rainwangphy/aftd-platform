import AFTD.Prelude
import AFTD.Kb.Tcs.AffineForm
import AFTD.Kb.Tcs.AffineFormToFreeAlgebra
import AFTD.Kb.Tcs.NcABP

/-!
# ncabp_matrix

Topic: algebraic_complexity   Node: e5f6be09b63f

Provenance: formalization of a published result. Source: arXiv:2610.37677, Section 3.2

Given a commutative semiring F, parameters m, S : ℕ, and an ncABP A : NcABP F m S, ncabp_matrix A is the transition matrix in Matrix (Fin S) (Fin S) (FreeAlgebra F (Fin m)) whose (u, v) entry is affine_form_to_free_algebra (A.edge u v).
-/

/-- The transition matrix of an ncABP with entries in FreeAlgebra F (Fin m). -/
def ncabp_matrix {F : Type*} [CommSemiring F] {m S : ℕ} (A : NcABP F m S) :
    Matrix (Fin S) (Fin S) (FreeAlgebra F (Fin m)) := fun u v => affine_form_to_free_algebra (A.edge u v)
