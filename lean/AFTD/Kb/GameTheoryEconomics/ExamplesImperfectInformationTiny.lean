import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationState
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationRootAction
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationP1Action
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationPlayer
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationInstFintypeState
import AFTD.Kb.GameTheoryEconomics.ExamplesImperfectInformationInfo

/-!
# Examples.ImperfectInformation.tiny

Topic: equilibria   Node: 1902664baeec

Provenance: formalization of a published result. Source: EconCSLib, `Examples.ImperfectInformation.tiny`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A tiny imperfect-information game where player 1 cannot distinguish two singleton-action states reached after player 0's root choice.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A tiny imperfect-information game where player 1 cannot distinguish two singleton-action states reached after player 0's root choice. -/
def Examples.ImperfectInformation.tiny : FiniteImperfectGame Player ℤ where
  State := State
  InfoSet := Info
  Action
    | .root => RootAction
    | .left => P1Action
    | .right => P1Action
    | .stop => PEmpty
  next
    | .root, RootAction.L => .left
    | .root, RootAction.R => .right
    | .left, P1Action.Stop => .stop
    | .right, P1Action.Stop => .stop
  init := .root
  mover
    | .root => some .P0
    | .left => some .P1
    | .right => some .P1
    | .stop => none
  info
    | .left => some .hiddenChoice
    | .right => some .hiddenChoice
    | _ => none
  payoff _ _ := 0
