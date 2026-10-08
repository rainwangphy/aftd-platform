import AFTD.Prelude

/-!
# Set.SymmOn

Topic: computability   Node: 90ff2d688fd2

Provenance: formalization of a published result. Source: CSLib, `Set.SymmOn`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`SymmOn s r` is true when a relation `r` is symmetric on its restriction to a set `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- `SymmOn s r` is true when a relation `r` is symmetric on its restriction to a set `s`. -/
def Set.SymmOn (s : Set α) (r : α → α → Prop) : Prop :=
  ∀ a ∈ s, ∀ b ∈ s, r a b → r b a
