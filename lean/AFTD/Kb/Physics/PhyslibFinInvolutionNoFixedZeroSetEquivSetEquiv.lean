import AFTD.Prelude

/-!
# Physlib.Fin.involutionNoFixedZeroSetEquivSetEquiv

Topic: classical_mechanics   Node: 94c09dced683

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixedZeroSetEquivSetEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The condition on fixed point free involutions of `Fin n.succ` for a fixed value of `f 0` given an equivalence `e`, can be modified so that only the condition on `f 0` is up-to the equivalence `e`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- The condition on fixed point free involutions of `Fin n.succ` for a fixed value of `f 0` given an equivalence `e`, can be modified so that only the condition on `f 0` is up-to the equivalence `e`. -/
def Physlib.Fin.involutionNoFixedZeroSetEquivSetEquiv {n : ℕ} (k : Fin n)
    (e : Fin n.succ ≃ Fin n.succ) :
    {f : Fin n.succ → Fin n.succ // Function.Involutive (e.symm ∘ f ∘ e) ∧
    (∀ i, (e.symm ∘ f ∘ e) i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} ≃
    {f : Fin n.succ → Fin n.succ // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} := by
  refine Equiv.subtypeEquivRight fun f ↦ ?_
  have h1 : Function.Involutive (⇑e.symm ∘ f ∘ ⇑e) ↔ Function.Involutive f := by
    apply Iff.intro <;> intro h i
    · simpa using h (e.symm i)
    · simp [h (e i)]
  rw [h1]
  simp only [succ_eq_add_one, Function.comp_apply, ne_eq, and_congr_right_iff, and_congr_left_iff]
  intro h1 h2
  apply Iff.intro
  · intro h i
    simpa using h (e.symm i)
  · intro h i
    have hi := h (e i)
    by_contra hn
    nth_rewrite 2 [← hn] at hi
    simp at hi
