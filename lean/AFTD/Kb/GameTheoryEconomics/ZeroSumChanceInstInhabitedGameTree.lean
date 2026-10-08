import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTree

/-!
# ZeroSumChance.instInhabitedGameTree

Topic: equilibria   Node: 98ed5b224a1a

Provenance: formalization of a published result. Source: EconCSLib, `ZeroSumChance.instInhabitedGameTree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/ZeroSumGameTreeWithChance.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ZeroSumChance.instInhabitedGameTree
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
instance ZeroSumChance.instInhabitedGameTree : Inhabited GameTree := ⟨.Leaf 0⟩
