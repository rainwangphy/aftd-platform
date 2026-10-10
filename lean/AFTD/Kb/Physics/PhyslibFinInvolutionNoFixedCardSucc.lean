import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInstFintypeSubtypeForallFinAndInvolutiveForallNePhyslib
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedZeroEquivProd

/-!
# Physlib.Fin.involutionNoFixed_card_succ

Topic: classical_mechanics   Node: c93315af58b7

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixed_card_succ`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.Fin.involutionNoFixed_card_succ
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
lemma Physlib.Fin.involutionNoFixed_card_succ {n : ℕ} :
    Fintype.card
    {f : Fin n.succ.succ → Fin n.succ.succ // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    = n.succ *
    Fintype.card {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} := by
  simp [Fintype.card_congr involutionNoFixedZeroEquivProd]
