import AFTD.Prelude

/-!
# Set.ReflOn

Topic: computability   Node: af7134405f9a

Provenance: formalization of a published result. Source: CSLib, `Set.ReflOn`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`ReflOn s r` is true when a relation `r` is reflexive on its restriction to a set `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- `ReflOn s r` is true when a relation `r` is reflexive on its restriction to a set `s`. -/
def Set.ReflOn (s : Set α) (r : α → α → Prop) : Prop :=
  ∀ a ∈ s, r a a

-- these names are used in the literature, so we provide them as `abbrev`
