import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTreeIsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.IsNashAt

Topic: equilibria   Node: 545927f6a2cf

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsNashAt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Root-scoped Nash equilibrium predicate for a fixed `GameTree` root. This is definitionally the existing `IsNashEquilibrium`, with the requested root-first API name for users who want to state equilibrium at a particular subgame rather than quantify over every subtree.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GameTree in
variable {N U : Type*} [TotalPreorder U] in
/-- Root-scoped Nash equilibrium predicate for a fixed `GameTree` root. This is definitionally the existing `IsNashEquilibrium`, with the requested root-first API name for users who want to state equilibrium at a particular subgame rather than quantify over every subtree. -/
abbrev GameTree.IsNashAt (σ : Strategy N U) (g : GameTree N U) : Prop :=
  GameTree.IsNashEquilibrium σ g
