import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstFunLikeOmegaSequenceNat
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.tail

Topic: algorithms   Node: 68a416e0be63

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.tail`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Tail of an ω-sequence: `ωSequence.tail (h :: t) = t`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- Tail of an ω-sequence: `ωSequence.tail (h :: t) = t`. -/
def Cslib.ωSequence.tail (s : ωSequence α) : ωSequence α := fun i => s (i + 1)
