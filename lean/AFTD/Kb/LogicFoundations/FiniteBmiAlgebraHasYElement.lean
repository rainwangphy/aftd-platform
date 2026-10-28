import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsBElement
import AFTD.Kb.LogicFoundations.BmiIsMElement
import AFTD.Kb.LogicFoundations.BmiIsIElement
import AFTD.Kb.LogicFoundations.BmiIsYElement
import AFTD.Kb.LogicFoundations.BmiIsLeftUnitB
import AFTD.Kb.LogicFoundations.BmiAssocOfIsBOfLeftUnit
import AFTD.Kb.LogicFoundations.BmiIdempotentOfAssocOfIsMOfIsI
import AFTD.Kb.LogicFoundations.BmiIsYElementOfIsIElementOfIdempotent

/-!
# finite_bmi_algebra_has_y_element

Topic: proof_theory   Node: 609e9ff52ad5

Provenance: formalization of a published result. Source: arXiv:2610.37108 Corollary 3.5 -- Finite BM-algebras and fixed-point combinators

Every finite $\mathbf{BMI}$-algebra has a $Y$-element: let $(A, \cdot)$ be a finite magma equipped with elements $B, M, I \in A$ such that $B$ is a $B$-element, $M$ is an $M$-element, and $I$ is an $I$-element; then there exists an element $Y \in A$ such that $Yx = x(Yx)$ for all $x \in A$.
-/

/-- Every finite BMI-algebra has a Y-element (fixed-point combinator element). -/
theorem finite_bmi_algebra_has_y_element {A : Type*} [Mul A] [Fintype A]
    (B M I : A) (hB : bmi_is_b_element B) (hM : bmi_is_m_element M) (hI : bmi_is_i_element I) :
    ∃ Y : A, bmi_is_y_element Y := by
  have hBunit : ∀ x : A, B * x = x := bmi_is_left_unit_b B I hB hI
  have hassoc : ∀ x y z : A, (x * y) * z = x * (y * z) :=
    bmi_assoc_of_is_b_of_left_unit B hB hBunit
  have hidem : ∀ x : A, x * x = x := bmi_idempotent_of_assoc_of_is_m_of_is_i hassoc M I hM hI
  exact ⟨I, bmi_is_y_element_of_is_i_element_of_idempotent I hI hidem⟩
