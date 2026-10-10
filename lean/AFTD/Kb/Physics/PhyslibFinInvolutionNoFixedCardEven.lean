import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInstFintypeSubtypeForallFinAndInvolutiveForallNePhyslib
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedCardMulTwo

/-!
# Physlib.Fin.involutionNoFixed_card_even

Topic: classical_mechanics   Node: 9ca6fd3aceac

Provenance: formalization of a published result. Source: Physlib, `Physlib.Fin.involutionNoFixed_card_even`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.Fin.involutionNoFixed_card_even
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Nat in
lemma Physlib.Fin.involutionNoFixed_card_even : (n : ℕ) → (he : Even n) →
    Fintype.card {f : Fin n → Fin n // Function.Involutive f ∧ (∀ i, f i ≠ i)} = (n - 1)‼ := by
  intro n he
  obtain ⟨r, hr⟩ := he
  have hr' : n = 2 * r := by omega
  subst hr'
  exact involutionNoFixed_card_mul_two r
