import AFTD.Prelude

/-!
# Relation.transRight

Topic: computability   Node: c41bc01f54de

Provenance: formalization of a published result. Source: CSLib, `Relation.transRight`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A subrelation lifts to transitivity on the right of the relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A subrelation lifts to transitivity on the right of the relation. -/
@[implicit_reducible]
def Relation.transRight (s r : α → α → Prop) [IsTrans α r] (h : s ≤ r) : Trans r s r where
  trans hab hbc := _root_.trans hab (h _ _ hbc)
