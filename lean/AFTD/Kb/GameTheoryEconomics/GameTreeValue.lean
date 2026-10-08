import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.ListArgMaxOn
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.ZeroSumChanceGameTreeValue

/-!
# GameTree.value

Topic: equilibria   Node: 87d48bed2169

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.value`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BackwardInduction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

GameTree.value
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [TotalPreorder U] [DecidableLE U] in
mutual
def GameTree.value : GameTree N U → (N → U)
    | Leaf p => p
    | Node m h t =>
        let hv := value h
        let tv := valueList t
        List.argMaxOn (fun v => v m) hv tv
def GameTree.valueList : List (GameTree N U) → List (N → U)
    | [] => []
    | x :: xs => value x :: valueList xs
end
