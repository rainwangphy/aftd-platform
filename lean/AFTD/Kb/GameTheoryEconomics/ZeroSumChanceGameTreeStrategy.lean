import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTree
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceSelect
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceInstInhabitedGameTree
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# ZeroSumChance.GameTree.Strategy

Topic: equilibria   Node: c1b33efdb54a

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.GameTree.Strategy`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pure strategy is a function that, given a player's decision node, selects one of the two branches. `Strategy ≝ GameTree → GameTree → Select`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A pure strategy is a function that, given a player's decision node, selects one of the two branches. `Strategy ≝ GameTree → GameTree → Select`. -/
abbrev ZeroSumChance.GameTree.Strategy := GameTree → GameTree → Select
