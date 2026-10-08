import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstFunLikeOmegaSequenceNat
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence
import AFTD.Kb.Tcs.CslibOmegaSequenceInstInhabited

/-!
# Cslib.ωSequence.instIsEmpty

Topic: algorithms   Node: ac781cb04b81

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.instIsEmpty`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Init.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.ωSequence.instIsEmpty
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
open Nat Function Option in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
variable (m n : ℕ) (x y : List α) (a b : ωSequence α) in
instance Cslib.ωSequence.instIsEmpty [h : IsEmpty α] : IsEmpty (ωSequence α) where
  false xs := IsEmpty.false (xs 0)
