import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtree
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.G

/-!
# GameTree.HasOnlyRootSubgames

Topic: equilibria   Node: 4da93b3c9322

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.HasOnlyRootSubgames`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTreeNE.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A fixed `GameTree` has no proper subgames when every subtree is the root itself. This is the pure finite-tree analogue of having no nontrivial subgames.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [TotalPreorder U] in
/-- A fixed `GameTree` has no proper subgames when every subtree is the root itself. This is the pure finite-tree analogue of having no nontrivial subgames. -/
def GameTree.HasOnlyRootSubgames (g : GameTree N U) : Prop :=
  ∀ s : GameTree N U, Subtree s g → s = g
