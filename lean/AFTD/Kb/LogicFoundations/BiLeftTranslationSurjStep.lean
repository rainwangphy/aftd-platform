import AFTD.Prelude
import AFTD.Kb.LogicFoundations.BmiIsBElement
import AFTD.Kb.LogicFoundations.BmiIsIElement

/-!
# bi_left_translation_surj_step

Topic: proof_theory   Node: 33120ce403f3

Provenance: helper lemma. arXiv:2610.37108 Proposition 3.1

In any magma with a B-element B and an I-element I, for any element a, the left translation by ((B * a) * I) coincides with the left translation by a: ((B * a) * I) * x = a * x for all x.
-/

/-- In a magma with a B-element and an I-element, ((Ba)I)x = ax for all x. -/
theorem bi_left_translation_surj_step {A : Type*} [Mul A]
    (B I : A) (hB : bmi_is_b_element B) (hI : bmi_is_i_element I) (a : A) :
    ∀ x : A, (B * a * I) * x = a * x := by
  intro x
  rw [hB, hI]
