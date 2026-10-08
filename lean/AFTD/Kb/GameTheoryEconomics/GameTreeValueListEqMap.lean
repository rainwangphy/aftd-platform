import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeValue
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.valueList_eq_map

Topic: equilibria   Node: 3bc8664eb908

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.valueList_eq_map`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/BackwardInduction.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`valueList l` is exactly `l.map value`. Useful for rewriting.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N U : Type*} [TotalPreorder U] [DecidableLE U] in
/-- `valueList l` is exactly `l.map value`. Useful for rewriting. -/
theorem GameTree.valueList_eq_map (l : List (GameTree N U)) :
    valueList l = l.map value := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp [valueList, ih]
