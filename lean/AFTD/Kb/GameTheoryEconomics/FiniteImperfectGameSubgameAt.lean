import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame

/-!
# FiniteImperfectGame.subgameAt

Topic: equilibria   Node: 47332fbbecef

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.subgameAt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The subgame starting at state `s`: same finite game data with a different initial state. Extra validity conditions, such as whether `s` is a legitimate imperfect-information subroot, can be imposed by theorem statements using this operation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- The subgame starting at state `s`: same finite game data with a different initial state. Extra validity conditions, such as whether `s` is a legitimate imperfect-information subroot, can be imposed by theorem statements using this operation. -/
def FiniteImperfectGame.subgameAt (s : G.State) : FiniteImperfectGame N U :=
  { G with init := s }
