import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceTail
import AFTD.Kb.Tcs.CslibOmegaSequenceCons
import AFTD.Kb.Tcs.CslibOmegaSequenceEta
import AFTD.Kb.Tcs.CslibOmegaSequenceGetFun
import AFTD.Kb.Tcs.CslibOmegaSequenceGetZeroCons
import AFTD.Kb.Tcs.CslibOmegaSequenceHeadCons
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceInstInhabited
import AFTD.Kb.Tcs.CslibOmegaSequenceInstIsEmpty

/-!
# Cslib.ωSequence.tail_cons

Topic: algorithms   Node: 61dcbae7c78c

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.tail_cons`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Init.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Cslib.ωSequence.tail_cons
-/

set_option quotPrecheck false
open Cslib Cslib.ωSequence
@[inherit_doc] local infixr:67 " ::ω " => cons

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.ωSequence in
open Nat Function Option in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
variable (m n : ℕ) (x y : List α) (a b : ωSequence α) in
@[simp, grind =]
theorem Cslib.ωSequence.tail_cons (a : α) (s : ωSequence α) : tail (a ::ω s) = s :=
  rfl
