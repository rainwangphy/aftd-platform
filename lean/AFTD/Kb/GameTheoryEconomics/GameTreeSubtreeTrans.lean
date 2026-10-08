import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtree
import AFTD.Kb.GameTheoryEconomics.GameTree

/-!
# GameTree.Subtree.trans

Topic: equilibria   Node: 5f2e09f00646

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.Subtree.trans`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/GameTree.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The subtree relation is transitive. In game-theoretic terms, a subgame of a subgame is also a subgame of the original game.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} in
/-- The subtree relation is transitive. In game-theoretic terms, a subgame of a subgame is also a subgame of the original game. -/
theorem GameTree.Subtree.trans {r s g : GameTree N U} (hrs : Subtree r s) (hsg : Subtree s g) :
    Subtree r g := by
  induction hsg with
  | refl => exact hrs
  | inHead m h t _ ih => exact Subtree.inHead r m h t ih
  | inTail m h t hmem _ ih => exact Subtree.inTail r m h t hmem ih
