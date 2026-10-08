import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasFresh
import AFTD.Kb.Tcs.CslibHasFreshToInfinite
import AFTD.Kb.Tcs.CslibInstHasFreshOfInfinite

/-!
# Cslib.HasFresh.ofSucc

Topic: algorithms   Node: 0f2906faa3bd

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasFresh.ofSucc`. Lean proof by Fabrizio Montesi, Kenny Lau, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/HasFresh.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Construct a fresh element given a function `f` with `x < f x`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
/-- Construct a fresh element given a function `f` with `x < f x`. -/
@[implicit_reducible]
def Cslib.HasFresh.ofSucc {α : Type u} [Inhabited α] [SemilatticeSup α] (f : α → α) (hf : ∀ x, x < f x) :
    HasFresh α where
  fresh s := if hs : s.Nonempty then f (s.sup' hs id) else default
  fresh_notMem s h := if hs : s.Nonempty
    then not_le_of_gt (hf (s.sup' hs id)) <| by rw [dif_pos hs] at h; exact s.le_sup' id h
    else hs ⟨_, h⟩
