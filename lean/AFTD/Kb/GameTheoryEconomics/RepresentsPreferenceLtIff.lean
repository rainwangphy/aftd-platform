import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RepresentsPreference
import AFTD.Kb.GameTheoryEconomics.Strict

/-!
# RepresentsPreference.lt_iff

Topic: social_choice   Node: 9607e3c4118a

Provenance: formalization of a published result. Source: EconCSLib, `RepresentsPreference.lt_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A utility representation preserves strict preference.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A utility representation preserves strict preference. -/
theorem RepresentsPreference.lt_iff [Preorder A] [Preorder V'] {u : A → V'}
    (h : RepresentsPreference u) (a b : A) :
    a < b ↔ u a < u b := by
  rw [Preorder.lt_iff_le_not_ge, Preorder.lt_iff_le_not_ge, h.le_iff, h.le_iff]
