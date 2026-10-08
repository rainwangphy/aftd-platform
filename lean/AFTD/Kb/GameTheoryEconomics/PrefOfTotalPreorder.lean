import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.IsPreference
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# Pref.ofTotalPreorder

Topic: social_choice   Node: be3348f8ece1

Provenance: formalization of a published result. Source: EconCSLib, `Pref.ofTotalPreorder`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Preference.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Bundle an explicit total preorder as a preference.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Bundle an explicit total preorder as a preference. -/
def Pref.ofTotalPreorder {A : Type*} (r : TotalPreorder A) : Pref A where
  rel := fun a b => @LE.le A r.toPreorder.toLE a b
  prop :=
    { reflexive := fun a => r.le_refl a
      transitive := fun _ _ _ => r.le_trans _ _ _
      total := fun a b => r.le_total a b }
