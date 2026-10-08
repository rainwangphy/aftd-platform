import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGame
import AFTD.Kb.GameTheoryEconomics.FiniteImperfectGameSubgameAt

/-!
# FiniteImperfectGame.subgameAt_init

Topic: equilibria   Node: 0b68bcbbf401

Provenance: formalization of a published result. Source: EconCSLib, `FiniteImperfectGame.subgameAt_init`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ImperfectInformation.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The initial state of `subgameAt` is the chosen root.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : FiniteImperfectGame N U) in
/-- The initial state of `subgameAt` is the chosen root. -/
theorem FiniteImperfectGame.subgameAt_init (s : G.State) : (G.subgameAt s).init = s := rfl
