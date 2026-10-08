import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceMap
import AFTD.Kb.Tcs.CslibOmegaSequenceCons
import AFTD.Kb.Tcs.CslibOmegaSequenceHead
import AFTD.Kb.Tcs.CslibOmegaSequenceTail
import AFTD.Kb.Tcs.CslibOmegaSequenceEta
import AFTD.Kb.Tcs.CslibOmegaSequenceTailMap
import AFTD.Kb.Tcs.CslibOmegaSequenceHeadMap
import AFTD.Kb.Tcs.CslibOmegaSequenceGetFun
import AFTD.Kb.Tcs.CslibOmegaSequenceGetZeroCons
import AFTD.Kb.Tcs.CslibOmegaSequenceHeadCons
import AFTD.Kb.Tcs.CslibOmegaSequenceTailCons
import AFTD.Kb.Tcs.CslibOmegaSequenceGetDrop
import AFTD.Kb.Tcs.CslibOmegaSequenceDropDrop
import AFTD.Kb.Tcs.CslibOmegaSequenceGetTail
import AFTD.Kb.Tcs.CslibOmegaSequenceTailDrop'
import AFTD.Kb.Tcs.CslibOmegaSequenceDropTail'
import AFTD.Kb.Tcs.CslibOmegaSequenceGetSuccCons
import AFTD.Kb.Tcs.CslibOmegaSequenceGetConsAppendZero
import AFTD.Kb.Tcs.CslibOmegaSequenceAppendEqCons
import AFTD.Kb.Tcs.CslibOmegaSequenceDropZero
import AFTD.Kb.Tcs.CslibOmegaSequenceGetMap
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceInstInhabited
import AFTD.Kb.Tcs.CslibOmegaSequenceInstIsEmpty

/-!
# Cslib.ωSequence.map_eq

Topic: algorithms   Node: 51392aa1bd84

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.map_eq`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Init.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.ωSequence.map_eq
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
variable (f : α → β) in
theorem Cslib.ωSequence.map_eq (s : ωSequence α) : map f s = f (head s) ::ω map f (tail s) := by
  rw [← ωSequence.eta (map f s), tail_map, head_map]
