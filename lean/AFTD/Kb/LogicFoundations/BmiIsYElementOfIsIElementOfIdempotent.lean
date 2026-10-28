import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsIElement
import AFTD.Kb.LogicFoundations.BmiIsYElement

/-!
# bmi_is_y_element_of_is_i_element_of_idempotent

Topic: proof_theory   Node: 99df5bbb9dbd

Provenance: formalization of a published result. Source: arXiv:2610.37108 Corollary 3.5 -- Finite BM-algebras and fixed-point combinators

In any idempotent magma, every left unit $I$ (satisfying $Ix = x$ for all $x$) is a $Y$-element: $Ix = x(Ix)$ for all $x$.
-/

/-- Any I-element (left unit) in an idempotent magma is a Y-element. -/
theorem bmi_is_y_element_of_is_i_element_of_idempotent {A : Type*} [Mul A]
    (I : A) (hI : bmi_is_i_element I) (hidem : ∀ x : A, x * x = x) :
    bmi_is_y_element I := by
  intro x
  rw [hI, hidem]
