import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsBElement
import AFTD.Kb.LogicFoundations.BmiIsMElement
import AFTD.Kb.LogicFoundations.BmiIsIElement
import AFTD.Kb.LogicFoundations.BmiIsLeftUnitB
import AFTD.Kb.LogicFoundations.BmiAssocOfIsBOfLeftUnit
import AFTD.Kb.LogicFoundations.BmiIdempotentOfAssocOfIsMOfIsI
import AFTD.Kb.LogicFoundations.BmiIsLeftUnitMOfIsMOfIdempotent

/-!
# finite_bmi_algebra_is_idempotent_semigroup_with_left_units

Topic: proof_theory   Node: 3e69b3a8349e

Provenance: formalization of a published result. Source: arXiv:2610.37108 Theorem 3.3

Every finite BMI-algebra is an idempotent semigroup with B, M, and I as left units: let $(A, \cdot)$ be a finite magma equipped with elements $B, M, I \in A$ such that $B$ is a $B$-element ($((Bx)y)z = x(yz)$ for all $x, y, z \in A$), $M$ is an $M$-element ($Mx = xx$ for all $x \in A$), and $I$ is an $I$-element ($Ix = x$ for all $x \in A$). Then the operation is associative ($(xy)z = x(yz)$ for all $x, y, z \in A$), every element is idempotent ($xx = x$ for all $x \in A$), and $B$, $M$, and $I$ are left units of $(A, \cdot)$ ($Bx = x$, $Mx = x$, and $Ix = x$ for all $x \in A$).
-/

/-- Every finite BMI-algebra is an idempotent semigroup with left units B, M, and I (arXiv:2610.37108 Theorem 3.3). -/
theorem finite_bmi_algebra_is_idempotent_semigroup_with_left_units
    {A : Type*} [Mul A] [Fintype A]
    (B M I : A) (hB : bmi_is_b_element B) (hM : bmi_is_m_element M) (hI : bmi_is_i_element I) :
    (∀ x y z : A, (x * y) * z = x * (y * z)) ∧
    (∀ x : A, x * x = x) ∧
    (∀ x : A, B * x = x) ∧
    (∀ x : A, M * x = x) ∧
    (∀ x : A, I * x = x) := by
  have hBu : ∀ x : A, B * x = x := bmi_is_left_unit_b B I hB hI
  have hassoc : ∀ x y z : A, (x * y) * z = x * (y * z) :=
    bmi_assoc_of_is_b_of_left_unit B hB hBu
  have hidem : ∀ x : A, x * x = x :=
    bmi_idempotent_of_assoc_of_is_m_of_is_i hassoc M I hM hI
  have hMu : ∀ x : A, M * x = x :=
    bmi_is_left_unit_m_of_is_m_of_idempotent M hM hidem
  exact ⟨hassoc, hidem, hBu, hMu, hI⟩
