import AFTD.Prelude

/-!
# Relation.Commute

Topic: computability   Node: d331058a541b

Provenance: formalization of a published result. Source: CSLib, `Relation.Commute`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Generalization of `Confluent` to two relations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Generalization of `Confluent` to two relations. -/
def Relation.Commute (r₁ r₂ : α → α → Prop) := ∀ {x y₁ y₂},
  ReflTransGen r₁ x y₁ → ReflTransGen r₂ x y₂ → ∃ z, ReflTransGen r₂ y₁ z ∧ ReflTransGen r₁ y₂ z
