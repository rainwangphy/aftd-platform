import AFTD.Prelude

/-!
# Relation.StronglyConfluent

Topic: computability   Node: 697a2371ef4f

Provenance: formalization of a published result. Source: CSLib, `Relation.StronglyConfluent`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation is strongly confluent when single steps are reflexive- and multi-joinable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation is strongly confluent when single steps are reflexive- and multi-joinable. -/
abbrev Relation.StronglyConfluent (r : α → α → Prop) :=
  ∀ {x y₁ y₂}, r x y₁ → r x y₂ → ∃ z, ReflGen r y₁ z ∧ ReflTransGen r y₂ z
