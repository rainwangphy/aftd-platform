import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence

/-!
# Cslib.instCoeForallNatωSequence

Topic: algorithms   Node: 6b36f98dbeb7

Provenance: formalization of a published result. Source: CSLib, `Cslib.instCoeForallNatωSequence`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.instCoeForallNatωSequence
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
instance Cslib.instCoeForallNatωSequence : Coe (ℕ → α) (ωSequence α) where
  coe f := ⟨f⟩
