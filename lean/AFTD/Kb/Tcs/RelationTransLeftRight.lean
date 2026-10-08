import AFTD.Prelude

/-!
# Relation.transLeftRight

Topic: computability   Node: 295baa7b6596

Provenance: formalization of a published result. Source: CSLib, `Relation.transLeftRight`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pair of subrelations lifts to transitivity on the relation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A pair of subrelations lifts to transitivity on the relation. -/
@[implicit_reducible]
def Relation.transLeftRight (s s' r : α → α → Prop) [IsTrans α r] (h : s ≤ r) (h' : s' ≤ r) :
    Trans s s' r where
  trans hab hbc := _root_.trans (h _ _ hab) (h' _ _ hbc)
