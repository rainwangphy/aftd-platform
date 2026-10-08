import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# PrefProfile

Topic: social_choice   Node: c8d6ab979051

Provenance: formalization of a published result. Source: EconCSLib, `PrefProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A preference profile assigns each agent a bundled preference.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A preference profile assigns each agent a bundled preference. -/
def PrefProfile (N A : Type*) := N → Pref A
