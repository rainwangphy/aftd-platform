import AFTD.Prelude

/-!
# Relation.instCoeDepForallForallPropForallElemForall_cslib

Topic: computability   Node: 3b256a8f4fff

Provenance: formalization of a published result. Source: CSLib, `Relation.instCoeDepForallForallPropForallElemForall_cslib`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.instCoeDepForallForallPropForallElemForall_cslib
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[nolint defsWithUnderscore]
instance Relation.instCoeDepForallForallPropForallElemForall_cslib (r : α → α → Prop) (s : Set α) : CoeDep (α → α → Prop) r (s → s → Prop) where
  coe a b := r a b
