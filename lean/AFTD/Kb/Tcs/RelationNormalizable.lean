import AFTD.Prelude
import AFTD.Kb.Tcs.RelationNormal

/-!
# Relation.Normalizable

Topic: computability   Node: 9d446b3f6509

Provenance: formalization of a published result. Source: CSLib, `Relation.Normalizable`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An element is normalizable if it is related to a normal element.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An element is normalizable if it is related to a normal element. -/
abbrev Relation.Normalizable (r : α → α → Prop) (x : α) : Prop :=
  ∃ n, ReflTransGen r x n ∧ Normal r n
