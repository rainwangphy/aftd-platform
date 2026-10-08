import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence

/-!
# Cslib.instFunLikeωSequenceNat

Topic: algorithms   Node: 483f253f6518

Provenance: formalization of a published result. Source: CSLib, `Cslib.instFunLikeωSequenceNat`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.instFunLikeωSequenceNat
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
set_option linter.tacticAnalysis.verifyGrindOnly false in
instance Cslib.instFunLikeωSequenceNat : FunLike (ωSequence α) ℕ α where
  coe := ωSequence.get
  coe_injective := by grind only [ωSequence, Function.Injective]
