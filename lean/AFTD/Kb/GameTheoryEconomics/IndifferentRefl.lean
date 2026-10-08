import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Indifferent

/-!
# Indifferent.refl

Topic: social_choice   Node: d518ef5cc86d

Provenance: formalization of a published result. Source: EconCSLib, `Indifferent.refl`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Indifference is reflexive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} [Preorder A] in
/-- Indifference is reflexive. -/
theorem Indifferent.refl (a : A) : Indifferent a a := ⟨le_refl a, le_refl a⟩
