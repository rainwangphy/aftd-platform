import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPreference
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# Pref.ofLinearOrder

Topic: social_choice   Node: 7d9e5cf98429

Provenance: formalization of a published result. Source: EconCSLib, `Pref.ofLinearOrder`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bundle an explicit linear order as a preference.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Bundle an explicit linear order as a preference. -/
def Pref.ofLinearOrder {A : Type*} (r : LinearOrder A) : Pref A where
  rel := fun a b => @LE.le A r.toLE a b
  prop :=
    { reflexive := fun a => r.le_refl a
      transitive := fun _ _ _ => r.le_trans _ _ _
      total := fun a b => r.le_total a b }
