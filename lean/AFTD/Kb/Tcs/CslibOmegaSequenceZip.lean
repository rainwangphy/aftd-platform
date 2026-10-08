import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstFunLikeOmegaSequenceNat
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.zip

Topic: algorithms   Node: f3dcbaac317e

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.zip`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Zip two ω-sequences using a binary operation: `ωSequence n (ωSequence.zip f s₁ s₂) = f (ωSequence s₁) (ωSequence s₂)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- Zip two ω-sequences using a binary operation: `ωSequence n (ωSequence.zip f s₁ s₂) = f (ωSequence s₁) (ωSequence s₂)`. -/
def Cslib.ωSequence.zip (f : α → β → δ) (s₁ : ωSequence α) (s₂ : ωSequence β) : ωSequence δ :=
  fun n => f (s₁ n) (s₂ n)
