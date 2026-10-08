import AFTD.Prelude
import AFTD.Kb.Tcs.RelationReducible

/-!
# Relation.Normal

Topic: computability   Node: 6337aa58ff29

Provenance: formalization of a published result. Source: CSLib, `Relation.Normal`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An element is normal if it is not reducible.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An element is normal if it is not reducible. -/
abbrev Relation.Normal (r : α → α → Prop) (x : α) : Prop := ¬ Reducible r x
