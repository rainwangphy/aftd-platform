import AFTD.Prelude

/-!
# Relation.Diamond

Topic: computability   Node: 9ec941e85252

Provenance: formalization of a published result. Source: CSLib, `Relation.Diamond`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation has the diamond property when all reductions with a common origin are joinable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation has the diamond property when all reductions with a common origin are joinable -/
abbrev Relation.Diamond (r : α → α → Prop) := ∀ {a b c : α}, r a b → r a c → Join r b c
