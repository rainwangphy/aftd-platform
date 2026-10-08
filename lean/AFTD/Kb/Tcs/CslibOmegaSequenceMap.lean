import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstFunLikeOmegaSequenceNat
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.map

Topic: algorithms   Node: b5c3178d6b99

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.map`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Apply a function `f` to all elements of an ω-sequence `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- Apply a function `f` to all elements of an ω-sequence `s`. -/
def Cslib.ωSequence.map (f : α → β) (s : ωSequence α) : ωSequence β := fun n => f (s n)
