import AFTD.Prelude

/-!
# Physlib.Fin.involutionNoFixedEquivSum

Topic: classical_mechanics   Node: 29c229c8da23

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixedEquivSum`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixed point free involutions of `Fin n.succ` can be separated based on where they sent `0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- Fixed point free involutions of `Fin n.succ` can be separated based on where they sent `0`. -/
def Physlib.Fin.involutionNoFixedEquivSum {n : ℕ} :
    {f : Fin n.succ → Fin n.succ // Function.Involutive f
    ∧ ∀ i, f i ≠ i} ≃ Σ (k : Fin n), {f : Fin n.succ → Fin n.succ // Function.Involutive f
    ∧ (∀ i, f i ≠ i) ∧ f 0 = k.succ} where
  toFun f := ⟨(f.1 0).pred (f.2.2 0), ⟨f.1, f.2.1, by simpa using f.2.2⟩⟩
  invFun f := ⟨f.2.1, ⟨f.2.2.1, f.2.2.2.1⟩⟩
  left_inv f := rfl
  right_inv f := by ext <;> try aesop
