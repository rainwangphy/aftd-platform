import AFTD.Prelude
import AFTD.Kb.Tcs.RelationConfluent
import AFTD.Kb.Tcs.RelationTerminating

/-!
# Relation.Convergent

Topic: computability   Node: 4981224a4544

Provenance: formalization of a published result. Source: CSLib, `Relation.Convergent`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation is convergent when it is both confluent and terminating.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation is convergent when it is both confluent and terminating. -/
abbrev Relation.Convergent (r : α → α → Prop) := Confluent r ∧ Terminating r
