import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI

/-!
# Cslib.SKI.size

Topic: computability   Node: e7b6db763ea4

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.size`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Defs.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The size of an SKI term is its number of combinators.
-/

open Cslib.SKI
@[inherit_doc]
local infixl:100 " ⬝ " => app

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The size of an SKI term is its number of combinators. -/
def Cslib.SKI.size : SKI → Nat
  | S => 1
  | K => 1
  | I => 1
  | x ⬝ y => size x + size y
