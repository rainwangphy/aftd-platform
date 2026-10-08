import AFTD.Prelude

/-!
# Relation.UpTo

Topic: computability   Node: bb2ed9c8d021

Provenance: formalization of a published result. Source: CSLib, `Relation.UpTo`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The relation `r` 'up to' the relation `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The relation `r` 'up to' the relation `s`. -/
def Relation.UpTo (r s : α → α → Prop) : α → α → Prop := Comp s (Comp r s)
