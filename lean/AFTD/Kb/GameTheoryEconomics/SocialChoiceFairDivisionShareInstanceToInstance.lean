import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionShareInstance
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionInstance
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionAllocation
import AFTD.Kb.GameTheoryEconomics.IsPreference
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp

/-!
# SocialChoice.FairDivision.ShareInstance.toInstance

Topic: fair_division   Node: 478b05d697a9

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.FairDivision.ShareInstance.toInstance`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/FairDivision/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lift a no-externality fair-division instance to a fully general allocation-preference instance by comparing allocations pointwise through the share assigned to the evaluating agent.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Lift a no-externality fair-division instance to a fully general allocation-preference instance by comparing allocations pointwise through the share assigned to the evaluating agent. -/
def SocialChoice.FairDivision.ShareInstance.toInstance {N R S : Type*}
    (I : ShareInstance N R S) : Instance N R S where
  resource := I.resource
  feasible := I.feasible
  pref i :=
    { rel := fun A B => I.sharePref i (A i) (B i)
      prop :=
        { reflexive := fun A => I.sharePref i |>.prop.reflexive (A i)
          transitive := fun _ _ _ hAB hBC => I.sharePref i |>.prop.transitive hAB hBC
          total := fun A B => I.sharePref i |>.prop.total (A i) (B i) } }
