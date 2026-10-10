import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedZeroSetEquivSetOne
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedSetOne

/-!
# Physlib.Fin.involutionNoFixedZeroSetEquiv

Topic: classical_mechanics   Node: e5e119fe8a56

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixedZeroSetEquiv`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fixed point involutions of `Fin n.succ.succ` for fixed `f 0 = k.succ` are equivalent to fixed point involutions of `Fin n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- Fixed point involutions of `Fin n.succ.succ` for fixed `f 0 = k.succ` are equivalent to fixed point involutions of `Fin n`. -/
def Physlib.Fin.involutionNoFixedZeroSetEquiv {n : ℕ} (k : Fin n.succ) :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧
      (∀ i, f i ≠ i) ∧ f 0 = k.succ}
        ≃ {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} :=
  (involutionNoFixedZeroSetEquivSetOne k).trans involutionNoFixedSetOne
