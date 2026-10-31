import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsBElement
import AFTD.Kb.LogicFoundations.BmiIsIElement
import AFTD.Kb.LogicFoundations.BmiIsLeftUnitB
import AFTD.Kb.LogicFoundations.BmiAssocOfIsBOfLeftUnit
import AFTD.Kb.LogicFoundations.BiLeftTranslationSurjStep
import AFTD.Kb.LogicFoundations.BiLeftTranslationIter2Eq

/-!
# finite_bi_algebra_is_semigroup_with_left_units

Topic: proof_theory   Node: 1939c8a9e452

Provenance: formalization of a published result. Source: arXiv:2610.37108 Proposition 3.1

Every finite BI-algebra is a semigroup with B and I as left units: let (A, ·) be a finite magma equipped with elements B, I in A such that B is a B-element (((Bx)y)z = x(yz) for all x, y, z in A) and I is an I-element (Ix = x for all x in A). Then the binary operation is associative ((xy)z = x(yz) for all x, y, z in A), and both B and I are left units of (A, ·) (Bx = x and Ix = x for all x in A).
-/

/-- Every finite BI-algebra is a semigroup with B and I as left units. -/
theorem finite_bi_algebra_is_semigroup_with_left_units
    {A : Type*} [Mul A] [Fintype A]
    (B I : A) (hB : bmi_is_b_element B) (hI : bmi_is_i_element I) :
    (∀ x y z : A, (x * y) * z = x * (y * z)) ∧
    (∀ x : A, B * x = x) ∧
    (∀ x : A, I * x = x) := by
  have hBunit : ∀ x : A, B * x = x := bmi_is_left_unit_b B I hB hI
  have hIunit : ∀ x : A, I * x = x := hI
  exact ⟨bmi_assoc_of_is_b_of_left_unit B hB hBunit, hBunit, hIunit⟩
