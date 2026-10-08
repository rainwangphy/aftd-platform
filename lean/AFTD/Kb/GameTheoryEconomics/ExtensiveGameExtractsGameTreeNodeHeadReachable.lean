import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameExtractsGameTree
import AFTD.Kb.GameTheoryEconomics.ArenaReachable
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameActionListComplete

/-!
# ExtensiveGame.ExtractsGameTree.node_head_reachable

Topic: equilibria   Node: b04d5602dacb

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ExtractsGameTree.node_head_reachable`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

At an extracted decision node, the head child is reached by one Arena transition and itself has an extracted subtree.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : ExtensiveGame N U) in
/-- At an extracted decision node, the head child is reached by one Arena transition and itself has an extracted subtree. -/
theorem ExtensiveGame.ExtractsGameTree.node_head_reachable {s : G.State} {i : N}
    {headTree : GameTree N U} {tailTrees : List (GameTree N U)}
    (h : ExtractsGameTree G s (GameTree.Node i headTree tailTrees)) :
    ∃ head : G.Action s,
      Arena.Reachable G.toArena s (G.next s head) ∧
        ExtractsGameTree G (G.next s head) headTree := by
  cases h with
  | node s i head tail headTree tailTrees hm hcomplete hhead htail =>
      exact ⟨head, Arena.Reachable.step head (Arena.Reachable.refl _), hhead⟩
