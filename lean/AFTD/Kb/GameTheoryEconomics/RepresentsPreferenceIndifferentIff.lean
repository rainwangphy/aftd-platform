import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Indifferent
import AFTD.Kb.GameTheoryEconomics.RepresentsPreference

/-!
# RepresentsPreference.indifferent_iff

Topic: social_choice   Node: ba52568642f6

Provenance: formalization of a published result. Source: EconCSLib, `RepresentsPreference.indifferent_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A utility representation preserves indifference.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A utility representation preserves indifference. -/
theorem RepresentsPreference.indifferent_iff [Preorder A] [Preorder V'] {u : A → V'}
    (h : RepresentsPreference u) (a b : A) :
    Indifferent a b ↔ Indifferent (u a) (u b) :=
  ⟨fun ⟨h1, h2⟩ => ⟨(h.le_iff a b).mp h1, (h.le_iff b a).mp h2⟩,
   fun ⟨h1, h2⟩ => ⟨(h.le_iff a b).mpr h1, (h.le_iff b a).mpr h2⟩⟩
