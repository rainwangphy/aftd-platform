import AFTD.Prelude

/-!
# Relation.ChurchRosser

Topic: computability   Node: 9c4478ee3e04

Provenance: formalization of a published result. Source: CSLib, `Relation.ChurchRosser`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation has the Church Rosser property when equivalence implies multi-joinability.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation has the Church Rosser property when equivalence implies multi-joinability. -/
abbrev Relation.ChurchRosser (r : α → α → Prop) := ∀ {x y}, EqvGen r x y → Join (ReflTransGen r) x y
