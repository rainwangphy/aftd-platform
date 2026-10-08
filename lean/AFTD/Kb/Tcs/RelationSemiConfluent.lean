import AFTD.Prelude

/-!
# Relation.SemiConfluent

Topic: computability   Node: 64ce6b9c9fb0

Provenance: formalization of a published result. Source: CSLib, `Relation.SemiConfluent`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation is semi-confluent when single and multiple steps with common origin are multi-joinable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation is semi-confluent when single and multiple steps with common origin are multi-joinable. -/
abbrev Relation.SemiConfluent (r : α → α → Prop) :=
  ∀ {x y₁ y₂}, ReflTransGen r x y₂ → r x y₁ → Join (ReflTransGen r) y₁ y₂
