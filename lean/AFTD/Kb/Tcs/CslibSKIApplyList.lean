import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI

/-!
# Cslib.SKI.applyList

Topic: computability   Node: da8ac5e1f0e0

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.applyList`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Defs.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Apply a term to a list of terms
-/

open Cslib.SKI
@[inherit_doc]
local infixl:100 " ⬝ " => app

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Apply a term to a list of terms -/
def Cslib.SKI.applyList (f : SKI) (xs : List SKI) : SKI := List.foldl (· ⬝ ·) f xs
