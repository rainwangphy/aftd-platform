import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.StrictlyDominatesWeakly
import AFTD.Kb.GameTheoryEconomics.WeaklyDominates
import AFTD.Kb.GameTheoryEconomics.IsStrictlyDominant
import AFTD.Kb.GameTheoryEconomics.IsWeaklyDominant
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# IsStrictlyDominant.isWeaklyDominant

Topic: equilibria   Node: 9faa8624fb35

Provenance: formalization of a published result. Source: EconCSLib, `IsStrictlyDominant.isWeaklyDominant`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/Dominance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A strictly dominant strategy is weakly dominant.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [DecidableEq N] [Preorder U] in
open EconCSLib.StrategicGame in
/-- A strictly dominant strategy is weakly dominant. -/
theorem IsStrictlyDominant.isWeaklyDominant {G : EconCSLib.StrategicGame N U} {i : N} {s : G.strategy i}
    [DecidableEq (G.strategy i)]
    (h : IsStrictlyDominant G i s) : IsWeaklyDominant G i s := by
  intro s'
  by_cases heq : s = s'
  · subst heq; intro σ; exact le_refl _
  · exact (h s' heq).weakly
