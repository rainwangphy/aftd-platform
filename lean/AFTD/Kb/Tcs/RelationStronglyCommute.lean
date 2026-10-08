import AFTD.Prelude

/-!
# Relation.StronglyCommute

Topic: computability   Node: 814230144d86

Provenance: formalization of a published result. Source: CSLib, `Relation.StronglyCommute`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Generalization of `StronglyConfluent` to two relations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Generalization of `StronglyConfluent` to two relations. -/
def Relation.StronglyCommute (r₁ r₂ : α → α → Prop) :=
  ∀ {x y₁ y₂}, r₁ x y₁ → r₂ x y₂ → ∃ z, ReflGen r₂ y₁ z ∧ ReflTransGen r₁ y₂ z
