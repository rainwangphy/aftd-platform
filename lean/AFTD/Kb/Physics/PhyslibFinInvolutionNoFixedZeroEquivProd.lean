import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedEquivSumSame

/-!
# Physlib.Fin.involutionNoFixedZeroEquivProd

Topic: classical_mechanics   Node: 7f3815df3d1c

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixedZeroEquivProd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ever fixed-point free involutions of `Fin n.succ.succ` can be decomposed into a element of `Fin n.succ` (where `0` is sent) and a fixed-point free involution of `Fin n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
/-- Ever fixed-point free involutions of `Fin n.succ.succ` can be decomposed into a element of `Fin n.succ` (where `0` is sent) and a fixed-point free involution of `Fin n`. -/
def Physlib.Fin.involutionNoFixedZeroEquivProd {n : ℕ} :
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    ≃ Fin n.succ × {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} :=
  involutionNoFixedEquivSumSame.trans <| .sigmaEquivProd ..
