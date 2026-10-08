import AFTD.Prelude
import AFTD.Kb.Tcs.RelationCod
import AFTD.Kb.Tcs.RelationMemCod

/-!
# Relation.cod_mono

Topic: computability   Node: f620b35f261e

Provenance: formalization of a published result. Source: CSLib, `Relation.cod_mono`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.cod_mono
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {β : Type*} {r : α → β → Prop} in
@[gcongr] lemma Relation.cod_mono (h : r₁ ≤ r₂) : cod r₁ ⊆ cod r₂ := fun b ⟨a, hab⟩ => ⟨a, h a b hab⟩
