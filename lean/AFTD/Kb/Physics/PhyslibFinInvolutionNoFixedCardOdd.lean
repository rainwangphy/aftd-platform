import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInstFintypeSubtypeForallFinAndInvolutiveForallNePhyslib
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedCardMulTwoPlusOne

/-!
# Physlib.Fin.involutionNoFixed_card_odd

Topic: classical_mechanics   Node: a07151e5352f

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixed_card_odd`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.Fin.involutionNoFixed_card_odd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
lemma Physlib.Fin.involutionNoFixed_card_odd : (n : ℕ) → (ho : Odd n) →
    Fintype.card {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} = 0 := by
  intro n ho
  obtain ⟨r, hr⟩ := ho
  subst hr
  exact involutionNoFixed_card_mul_two_plus_one r
