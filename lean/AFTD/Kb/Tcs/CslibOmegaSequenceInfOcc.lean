import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstFunLikeOmegaSequenceNat
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.infOcc

Topic: algorithms   Node: 3185229e66c9

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.infOcc`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/InfOcc.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The set of elements that appear infinitely often in an ω-sequence.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set Filter in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- The set of elements that appear infinitely often in an ω-sequence. -/
def Cslib.ωSequence.infOcc (xs : ωSequence α) : Set α :=
  { x | ∃ᶠ k in atTop, xs k = x }
