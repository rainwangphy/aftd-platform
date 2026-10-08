import AFTD.Prelude
import AFTD.Kb.Tcs.RelationNormalizable

/-!
# Relation.Normalizing

Topic: computability   Node: 5a872027127c

Provenance: formalization of a published result. Source: CSLib, `Relation.Normalizing`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation is normalizing when every element is normalizable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation is normalizing when every element is normalizable. -/
abbrev Relation.Normalizing (r : α → α → Prop) : Prop :=
  ∀ x, Normalizable r x
