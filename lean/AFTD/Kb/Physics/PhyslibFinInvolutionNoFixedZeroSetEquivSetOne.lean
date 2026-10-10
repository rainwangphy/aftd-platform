import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedZeroSetEquivEquiv
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedZeroSetEquivSetEquiv
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedZeroSetEquivEquiv'

/-!
# Physlib.Fin.involutionNoFixedZeroSetEquivSetOne

Topic: classical_mechanics   Node: e65b504de557

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixedZeroSetEquivSetOne`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixed point involutions of `Fin n.succ.succ` with `f 0 = k.succ` are equivalent to fixed point involutions with `f 0 = 1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- Fixed point involutions of `Fin n.succ.succ` with `f 0 = k.succ` are equivalent to fixed point involutions with `f 0 = 1`. -/
def Physlib.Fin.involutionNoFixedZeroSetEquivSetOne {n : ℕ} (k : Fin n.succ) :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧ f 0 = k.succ}
      ≃ {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧ f 0 = 1} := by
  refine (involutionNoFixedZeroSetEquivEquiv k (Equiv.swap k.succ 1)).trans ?_
  refine (involutionNoFixedZeroSetEquivSetEquiv k (Equiv.swap k.succ 1)).trans ?_
  refine (involutionNoFixedZeroSetEquivEquiv' k (Equiv.swap k.succ 1)).trans ?_
  refine Equiv.subtypeEquivRight ?_
  simp only [succ_eq_add_one, ne_eq, Equiv.swap_apply_left, and_congr_right_iff]
  intro f hi h1
  rw [Equiv.swap_apply_of_ne_of_ne]
  · exact Ne.symm (Fin.succ_ne_zero k)
  · exact Fin.zero_ne_one
