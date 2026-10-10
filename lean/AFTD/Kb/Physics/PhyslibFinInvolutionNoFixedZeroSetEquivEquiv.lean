import AFTD.Prelude

/-!
# Physlib.Fin.involutionNoFixedZeroSetEquivEquiv

Topic: classical_mechanics   Node: c67d33eccd66

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixedZeroSetEquivEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The condition on fixed point free involutions of `Fin n.succ` for a fixed value of `f 0`, can be modified by conjugation with an equivalence.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- The condition on fixed point free involutions of `Fin n.succ` for a fixed value of `f 0`, can be modified by conjugation with an equivalence. -/
def Physlib.Fin.involutionNoFixedZeroSetEquivEquiv {n : ℕ}
    (k : Fin n) (e : Fin n.succ ≃ Fin n.succ) :
    {f : Fin n.succ → Fin n.succ // Function.Involutive f ∧ (∀ i, f i ≠ i) ∧ f 0 = k.succ} ≃
    {f : Fin n.succ → Fin n.succ // Function.Involutive (e.symm ∘ f ∘ e) ∧
      (∀ i, (e.symm ∘ f ∘ e) i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} where
  toFun f := ⟨e ∘ f.1 ∘ e.symm, by
    intro i
    simp only [succ_eq_add_one, ne_eq, Function.comp_apply, Equiv.symm_apply_apply]
    rw [f.2.1], by simpa using f.2.2.1, by simpa using f.2.2.2⟩
  invFun f := ⟨e.symm ∘ f.1 ∘ e, by
    intro i
    simpa using f.2.1 i, by simpa using f.2.2.1, by simpa using f.2.2.2⟩
  left_inv f := by ext i; simp
  right_inv f := by ext i; simp
