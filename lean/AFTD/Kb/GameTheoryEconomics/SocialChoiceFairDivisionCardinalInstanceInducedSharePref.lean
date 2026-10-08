import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionCardinalInstance
import AFTD.Kb.GameTheoryEconomics.IsPreference
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# SocialChoice.FairDivision.CardinalInstance.inducedSharePref

Topic: fair_division   Node: 83e66cf83c60

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.CardinalInstance.inducedSharePref`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Cardinal.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The share preference induced by a cardinal utility, using the convention that higher utility means weakly better.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The share preference induced by a cardinal utility, using the convention that higher utility means weakly better. -/
def SocialChoice.FairDivision.CardinalInstance.inducedSharePref {N R S : Type*}
    (I : CardinalInstance N R S) : N → Pref S :=
  fun i =>
    { rel := fun s t => I.utility i t ≤ I.utility i s
      prop :=
        { reflexive := fun s => le_rfl
          transitive := fun _ _ _ hst htu => le_trans htu hst
          total := fun s t =>
            by
              rcases le_total (I.utility i s) (I.utility i t) with h | h
              · exact Or.inr h
              · exact Or.inl h } }
