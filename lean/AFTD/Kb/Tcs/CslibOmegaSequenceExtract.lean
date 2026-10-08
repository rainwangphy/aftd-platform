import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceTake
import AFTD.Kb.Tcs.CslibOmegaSequenceDrop
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.extract

Topic: algorithms   Node: a970d4183752

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.extract`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Get the list containing the elements of `xs` from position `m` to `n - 1`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- Get the list containing the elements of `xs` from position `m` to `n - 1`. -/
def Cslib.ωSequence.extract (xs : ωSequence α) (m n : ℕ) : List α :=
  take (n - m) (xs.drop m)
