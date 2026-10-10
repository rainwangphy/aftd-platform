import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedZeroSetEquivSetEquiv

/-!
# Physlib.Fin.involutionNoFixedZeroSetEquivEquiv'

Topic: classical_mechanics   Node: 8004dce9f84a

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixedZeroSetEquivEquiv'`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixed point free involutions of `Fin n.succ` fixing `(e.symm ∘ f ∘ e) = k.succ` for a given `e` are equivalent to fixing `f (e 0) = e k.succ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- Fixed point free involutions of `Fin n.succ` fixing `(e.symm ∘ f ∘ e) = k.succ` for a given `e` are equivalent to fixing `f (e 0) = e k.succ`. -/
def Physlib.Fin.involutionNoFixedZeroSetEquivEquiv' {n : ℕ} (k : Fin n) (e : Fin n.succ ≃ Fin n.succ) :
    {f : Fin n.succ → Fin n.succ // Function.Involutive f ∧
    (∀ i, f i ≠ i) ∧ (e.symm ∘ f ∘ e) 0 = k.succ} ≃
    {f : Fin n.succ → Fin n.succ // Function.Involutive f ∧
    (∀ i, f i ≠ i) ∧ f (e 0) = e k.succ} := by
  refine Equiv.subtypeEquivRight ?_
  simp only [succ_eq_add_one, ne_eq, Function.comp_apply, and_congr_right_iff]
  intro f hi h1
  exact Equiv.symm_apply_eq e
