import AFTD.Prelude
import AFTD.Kb.Tcs.WellFoundedOfTransGen

/-!
# WellFounded.iff_transGen

Topic: computability   Node: 3719324af17c

Provenance: formalization of a published result. Source: CSLib, `WellFounded.iff_transGen`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Confluence.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

WellFounded.iff_transGen
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {α : Type*} {r r₁ r₂ : α → α → Prop} in
@[simp, grind =]
theorem WellFounded.iff_transGen : WellFounded (Relation.TransGen r) ↔ WellFounded r :=
  ⟨ofTransGen, transGen⟩
