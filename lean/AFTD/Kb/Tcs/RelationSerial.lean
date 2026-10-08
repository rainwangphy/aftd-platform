import AFTD.Prelude

/-!
# Relation.Serial

Topic: computability   Node: b2f72e19a31d

Provenance: formalization of a published result. Source: CSLib, `Relation.Serial`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation `r` is serial if every element is `Reducible`, i.e. `Relator.LeftTotal`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation `r` is serial if every element is `Reducible`, i.e. `Relator.LeftTotal`. -/
class Relation.Serial (r : α → α → Prop) where
  serial : Relator.LeftTotal r
