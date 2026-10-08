import AFTD.Prelude
import AFTD.Kb.Tcs.RelationDiamond

/-!
# Relation.Confluent

Topic: computability   Node: 82f46a07be2b

Provenance: formalization of a published result. Source: CSLib, `Relation.Confluent`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation is confluent when its reflexive transitive closure has the diamond property.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation is confluent when its reflexive transitive closure has the diamond property. -/
abbrev Relation.Confluent (r : α → α → Prop) := Diamond (ReflTransGen r)
