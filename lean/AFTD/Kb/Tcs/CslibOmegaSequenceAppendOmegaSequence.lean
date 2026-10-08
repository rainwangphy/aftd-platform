import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceCons
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.appendωSequence

Topic: algorithms   Node: 63b2f2f927a6

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.appendωSequence`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Append an ω-sequence to a list.
-/

open Cslib.ωSequence
@[inherit_doc] local infixr:67 " ::ω " => cons

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- Append an ω-sequence to a list. -/
def Cslib.ωSequence.appendωSequence : List α → ωSequence α → ωSequence α
  | [], s => s
  | List.cons a l, s => a ::ω appendωSequence l s
