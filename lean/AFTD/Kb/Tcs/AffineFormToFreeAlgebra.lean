import AFTD.Prelude
import AFTD.Kb.Tcs.AffineForm

/-!
# affine_form_to_free_algebra

Topic: algebraic_complexity   Node: cf74a52ef54b

Provenance: formalization of a published result. Source: arXiv:2610.37677, Section 1.1

Given a commutative semiring F, a natural number m, and an affine form a : AffineForm F m, affine_form_to_free_algebra a is the element of FreeAlgebra F (Fin m) defined by algebraMap F (FreeAlgebra F (Fin m)) a.c0 + ∑ i : Fin m, algebraMap F (FreeAlgebra F (Fin m)) (a.c i) * FreeAlgebra.ι F i.
-/

/-- Canonical embedding of an affine linear form into FreeAlgebra F (Fin m). -/
def affine_form_to_free_algebra {F : Type*} [CommSemiring F] {m : ℕ} (a : AffineForm F m) :
    FreeAlgebra F (Fin m) := open BigOperators in algebraMap F (FreeAlgebra F (Fin m)) a.c0 + ∑ i : Fin m, algebraMap F (FreeAlgebra F (Fin m)) (a.c i) * FreeAlgebra.ι F i
