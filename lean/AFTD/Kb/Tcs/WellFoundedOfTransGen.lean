import AFTD.Prelude

/-!
# WellFounded.ofTransGen

Topic: computability   Node: 77a71f2e896a

Provenance: formalization of a published result. Source: CSLib, `WellFounded.ofTransGen`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Confluence.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WellFounded.ofTransGen
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r r₁ r₂ : α → α → Prop} in
theorem WellFounded.ofTransGen (trans_wf : WellFounded (Relation.TransGen r)) : WellFounded r := by
  grind [WellFounded.wellFounded_iff_has_min, Relation.TransGen]
