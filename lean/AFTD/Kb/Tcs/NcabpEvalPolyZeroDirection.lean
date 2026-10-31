import AFTD.Prelude
import AFTD.Kb.Tcs.AffineForm
import AFTD.Kb.Tcs.AffineFormToFreeAlgebra
import AFTD.Kb.Tcs.NcABP
import AFTD.Kb.Tcs.NcabpMatrix
import AFTD.Kb.Tcs.NcabpEvalPoly

/-!
# ncabp_eval_poly_zero_direction

Topic: algebraic_complexity   Node: 06b576bb210d

Provenance: helper lemma. arXiv:2610.37677, Theorem 1.1

Given a field F, natural numbers m, S, R, a matrix tuple T : Fin m → Matrix (Fin R) (Fin R) F, and an ncABP A : NcABP F m S such that ncabp_eval_poly A = 0, the evaluation (FreeAlgebra.lift F T) (ncabp_eval_poly A) equals 0.
-/

/-- Evaluating a vanishing ncABP polynomial at any matrix tuple produces the zero matrix. -/
theorem ncabp_eval_poly_zero_direction {F : Type*} [Field F] (m S R : ℕ)
    (T : Fin m → Matrix (Fin R) (Fin R) F) (A : NcABP F m S) (hA : ncabp_eval_poly A = 0) :
    (FreeAlgebra.lift F T) (ncabp_eval_poly A) = 0 := by
  rw [hA]
  exact map_zero _
