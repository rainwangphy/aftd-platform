import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.const

Topic: algorithms   Node: 8f2b9cc2b4ea

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.const`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The constant ω-sequence: `ωSequence n (ωSequence.const a) = a`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- The constant ω-sequence: `ωSequence n (ωSequence.const a) = a`. -/
def Cslib.ωSequence.const (a : α) : ωSequence α := fun (_ : ℕ) => a
