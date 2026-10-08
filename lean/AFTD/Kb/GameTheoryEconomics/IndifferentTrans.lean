import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Indifferent

/-!
# Indifferent.trans

Topic: social_choice   Node: b031359acec6

Provenance: formalization of a published result. Source: EconCSLib, `Indifferent.trans`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Indifference is transitive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {A : Type*} [Preorder A] in
/-- Indifference is transitive. -/
theorem Indifferent.trans {a b c : A} (h₁ : Indifferent a b) (h₂ : Indifferent b c) :
    Indifferent a c :=
  ⟨le_trans h₁.1 h₂.1, le_trans h₂.2 h₁.2⟩
