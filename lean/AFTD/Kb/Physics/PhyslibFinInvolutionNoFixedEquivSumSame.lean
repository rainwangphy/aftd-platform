import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedZeroSetEquivSetOne
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedEquivSum
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedZeroSetEquiv

/-!
# Physlib.Fin.involutionNoFixedEquivSumSame

Topic: classical_mechanics   Node: f4409fad110b

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixedEquivSumSame`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The type of fixed point free involutions of `Fin n.succ.succ` is equivalent to the sum of `Fin n.succ` copies of fixed point involutions of `Fin n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- The type of fixed point free involutions of `Fin n.succ.succ` is equivalent to the sum of `Fin n.succ` copies of fixed point involutions of `Fin n`. -/
def Physlib.Fin.involutionNoFixedEquivSumSame {n : ℕ} :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    ≃ Σ (_ : Fin n.succ), {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} :=
    involutionNoFixedEquivSum.trans <| .sigmaCongrRight involutionNoFixedZeroSetEquiv
