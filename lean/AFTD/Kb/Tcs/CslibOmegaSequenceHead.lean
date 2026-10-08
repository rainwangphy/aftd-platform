import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstFunLikeOmegaSequenceNat
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.head

Topic: algorithms   Node: 2a74f096b003

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.head`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Head of an ω-sequence: `ωSequence.head s = ωSequence s 0`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- Head of an ω-sequence: `ωSequence.head s = ωSequence s 0`. -/
abbrev Cslib.ωSequence.head (s : ωSequence α) : α := s 0
