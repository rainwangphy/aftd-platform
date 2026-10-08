import AFTD.Prelude
import AFTD.Kb.Tcs.RelationDom
import AFTD.Kb.Tcs.RelationMemDom

/-!
# Relation.dom_mono

Topic: computability   Node: 2527e499e060

Provenance: formalization of a published result. Source: CSLib, `Relation.dom_mono`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.dom_mono
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {β : Type*} {r : α → β → Prop} in
@[gcongr] lemma Relation.dom_mono (h : r₁ ≤ r₂) : dom r₁ ⊆ dom r₂ := fun a ⟨b, hab⟩ => ⟨b, h a b hab⟩
