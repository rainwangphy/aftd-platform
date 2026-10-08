import AFTD.Prelude

/-!
# Relation.emptyHRelation

Topic: computability   Node: 8b15bf803d8b

Provenance: formalization of a published result. Source: CSLib, `Relation.emptyHRelation`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The empty (heterogeneous) relation, which always returns `False`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The empty (heterogeneous) relation, which always returns `False`. -/
@[nolint unusedArguments]
def Relation.emptyHRelation {α : Sort u} {β : Sort v} (_ : α) (_ : β) := False
