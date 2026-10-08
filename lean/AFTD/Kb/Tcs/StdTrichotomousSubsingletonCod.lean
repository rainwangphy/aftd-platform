import AFTD.Prelude
import AFTD.Kb.Tcs.RelationCod
import AFTD.Kb.Tcs.RelationMemCod
import AFTD.Kb.Tcs.RelationCodEmpty
import AFTD.Kb.Tcs.RelationCodEqEmptyIff
import AFTD.Kb.Tcs.RelationCodInv
import AFTD.Kb.Tcs.RelationDomInv

/-!
# Std.Trichotomous.subsingleton_cod

Topic: computability   Node: 76e0b5f1ffba

Provenance: formalization of a published result. Source: CSLib, `Std.Trichotomous.subsingleton_cod`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Std.Trichotomous.subsingleton_cod
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
variable {β : Type*} {r : α → β → Prop} in
theorem Std.Trichotomous.subsingleton_cod (r : α → α → Prop) [Std.Trichotomous r] :
    Subsingleton ((cod r)ᶜ : Set α) := by
  constructor
  rintro ⟨b₁, _⟩ ⟨b₂, _⟩
  have := @Std.Trichotomous.rel_or_eq_or_rel_swap _ r _ b₁ b₂
  grind
