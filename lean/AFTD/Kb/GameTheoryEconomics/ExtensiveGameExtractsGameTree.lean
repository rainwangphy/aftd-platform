import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExtensiveGame
import AFTD.Kb.GameTheoryEconomics.Arena
import AFTD.Kb.GameTheoryEconomics.ControlledGame
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameIsTerminal
import AFTD.Kb.GameTheoryEconomics.ExtensiveGameActionListComplete

/-!
# ExtensiveGame.ExtractsGameTree

Topic: equilibria   Node: e25b37782238

Provenance: formalization of a published result. Source: EconCSLib, `ExtensiveGame.ExtractsGameTree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/FiniteArenaExtraction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

ExtensiveGame.ExtractsGameTree
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} (G : ExtensiveGame N U) in
mutual
inductive ExtensiveGame.ExtractsGameTree : G.State → GameTree N U → Prop where
    | leaf (s : G.State) (hs : G.isTerminal s) :
        ExtractsGameTree s (GameTree.Leaf (G.payoff s))
    | node (s : G.State) (i : N) (head : G.Action s) (tail : List (G.Action s))
        (headTree : GameTree N U) (tailTrees : List (GameTree N U))
        (hm : G.mover s = some i)
        (hcomplete : G.ActionListComplete s head tail)
        (hhead : ExtractsGameTree (G.next s head) headTree)
        (htail : ExtractsGameTreeList s tail tailTrees) :
        ExtractsGameTree s (GameTree.Node i headTree tailTrees)
inductive ExtensiveGame.ExtractsGameTreeList :
      (s : G.State) → List (G.Action s) → List (GameTree N U) → Prop where
    | nil (s : G.State) : ExtractsGameTreeList s [] []
    | cons (s : G.State) (head : G.Action s) (tail : List (G.Action s))
        (headTree : GameTree N U) (tailTrees : List (GameTree N U))
        (hhead : ExtractsGameTree (G.next s head) headTree)
        (htail : ExtractsGameTreeList s tail tailTrees) :
        ExtractsGameTreeList s (head :: tail) (headTree :: tailTrees)
end
