import AFTD.Prelude
import AFTD.Kb.Tcs.AffineForm
import AFTD.Kb.Tcs.AffineFormToFreeAlgebra
import AFTD.Kb.Tcs.NcABP
import AFTD.Kb.Tcs.NcabpMatrix
import AFTD.Kb.Tcs.NcabpEvalPoly

/-!
# is_ncabp_hitting_tuple

Topic: algebraic_complexity   Node: 8588283b841a

Provenance: formalization of a published result. Source: arXiv:2610.37677, Theorem 1.1

Given a field F and natural numbers m, S, R, a tuple of matrices T : Fin m → Matrix (Fin R) (Fin R) F is an ncABP hitting tuple if for every A : NcABP F m S, (FreeAlgebra.lift F T) (ncabp_eval_poly A) = 0 if and only if ncabp_eval_poly A = 0.
-/

/-- A tuple of R × R matrices is a hitting point of order R for ncABPs with S vertices. -/
def is_ncabp_hitting_tuple {F : Type*} [Field F] (m S R : ℕ)
    (T : Fin m → Matrix (Fin R) (Fin R) F) : Prop := ∀ (A : NcABP F m S),
    (FreeAlgebra.lift F T) (ncabp_eval_poly A) = 0 ↔ ncabp_eval_poly A = 0
