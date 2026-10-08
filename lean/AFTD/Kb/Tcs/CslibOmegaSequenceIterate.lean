import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.iterate

Topic: algorithms   Node: e5e3559a9a01

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.iterate`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Iterates of a function as an ω-sequence.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- Iterates of a function as an ω-sequence. -/
def Cslib.ωSequence.iterate (f : α → α) (a : α) : ωSequence α := fun n => f^[n] a
