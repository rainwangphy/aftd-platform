import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInstFintypeSubtypeForallFinAndInvolutiveForallNePhyslib
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedCardSucc

/-!
# Physlib.Fin.involutionNoFixed_card_mul_two

Topic: classical_mechanics   Node: 07e9149e1378

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixed_card_mul_two`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.Fin.involutionNoFixed_card_mul_two
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
lemma Physlib.Fin.involutionNoFixed_card_mul_two : (n : ℕ) →
    Fintype.card {f : Fin (2 * n) → Fin (2 * n) // Function.Involutive f ∧ (∀ i, f i ≠ i)}
    = (2 * n - 1)‼
  | 0 => rfl
  | Nat.succ n => by
    erw [involutionNoFixed_card_succ, involutionNoFixed_card_mul_two n]
    exact (Nat.doubleFactorial_add_one (Nat.mul 2 n)).symm
