import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsBElement
import AFTD.Kb.LogicFoundations.BmiIsIElement

/-!
# bi_left_translation_iter2_eq

Topic: proof_theory   Node: 1bd9a8deab9c

Provenance: helper lemma. arXiv:2610.37108 Proposition 3.1

In any magma with a B-element B and an I-element I, the left translations by ((B * I) * I) and ((I * I) * I) are equal: ((B * I) * I) * x = ((I * I) * I) * x for all x.
-/

/-- In a magma with a B-element and an I-element, ((BI)I)x = ((II)I)x for all x. -/
theorem bi_left_translation_iter2_eq {A : Type*} [Mul A]
    (B I : A) (hB : bmi_is_b_element B) (hI : bmi_is_i_element I) :
    ∀ x : A, (B * I * I) * x = (I * I * I) * x := by
  intro x
  rw [hB]
  repeat rw [hI]
