import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI
import AFTD.Kb.Tcs.CslibSKIApplyList

/-!
# Cslib.SKI.applyList_concat

Topic: computability   Node: 47a596c5b0f0

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.applyList_concat`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Defs.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.SKI.applyList_concat
-/

open Cslib.SKI
@[inherit_doc]
local infixl:100 " ⬝ " => app

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
lemma Cslib.SKI.applyList_concat (f : SKI) (ys : List SKI) (z : SKI) :
    f.applyList (ys ++ [z]) = f.applyList ys ⬝ z := by
  simp [applyList]
