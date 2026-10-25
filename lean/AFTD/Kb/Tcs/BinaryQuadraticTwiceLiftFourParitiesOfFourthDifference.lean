import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryFourParityElimination
import AFTD.Kb.Tcs.BinaryQuadraticDecomposableModLinearOfFourthDifference

/-!
# binary_quadratic_twice_lift_four_parities_of_fourth_difference

Topic: quantum   Node: cff363e47a9e

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

Under the fourth-difference condition, twice the binary quadratic lift has an explicit representation by four lifted linear forms and one even-coefficient linear correction modulo eight.
-/

theorem binary_quadratic_twice_lift_four_parities_of_fourth_difference {V : Type*}
    [AddCommGroup V] [Module (ZMod 2) V]
    (Q : QuadraticForm (ZMod 2) V)
    (hfour : ∀ u : Fin 4 → V,
      (∑ x : Fin 4 → ZMod 2,
        (-1 : ZMod 8) ^ (∑ i : Fin 4, (x i).val) *
          (2 * ((Q (∑ i : Fin 4, x i • u i)).val : ZMod 8))) = 0) :
    ∃ a b l : V →ₗ[ZMod 2] ZMod 2, ∀ v,
      2 * ((Q v).val : ZMod 8) =
        ((l v).val : ZMod 8) + ((l v+a v).val : ZMod 8) +
          ((l v+b v).val : ZMod 8) + ((l v+a v+b v).val : ZMod 8) -
            2 * ((a v+b v+l v).val : ZMod 8) := by
  obtain ⟨a,b,l,habl⟩ := binary_quadratic_decomposable_mod_linear_of_fourth_difference Q hfour
  refine ⟨a,b,l,?_⟩
  intro v
  rw [habl]
  have he := binary_four_parity_elimination (a v) (b v) (l v) (l v)
  simp only [CharTwo.add_self_eq_zero, ZMod.val_zero, Nat.cast_zero, mul_zero,
    zero_add] at he
  linear_combination -he
