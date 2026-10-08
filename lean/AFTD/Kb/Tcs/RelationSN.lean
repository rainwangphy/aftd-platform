import AFTD.Prelude

/-!
# Relation.SN

Topic: computability   Node: 95215bca6b23

Provenance: formalization of a published result. Source: CSLib, `Relation.SN`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An element `x` is `SN` (for strongly-normalising) for a relation `r` if it is accessible under the inverse of `r`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An element `x` is `SN` (for strongly-normalising) for a relation `r` if it is accessible under the inverse of `r`. -/
abbrev Relation.SN (r : α → α → Prop) := Acc (fun a b => r b a)
