import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSum
import AFTD.Kb.GameTheoryEconomics.GameTreeSubtree
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSumHead
import AFTD.Kb.GameTheoryEconomics.GameTreeIsZeroSumTailMem
import AFTD.Kb.Tcs.G

/-!
# GameTree.IsZeroSum.of_subtree

Topic: equilibria   Node: 2d591fa49839

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.IsZeroSum.of_subtree`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Zero-sumness is inherited by subgames.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Zero-sumness is inherited by subgames. -/
theorem GameTree.IsZeroSum.of_subtree {s g : GameTree (Fin 2) ℚ}
    (hzs : IsZeroSum g) (hsub : Subtree s g) : IsZeroSum s := by
  induction hsub with
  | refl => exact hzs
  | inHead m h t _ ih => exact ih (IsZeroSum.head hzs)
  | inTail m h t hmem _ ih => exact ih (IsZeroSum.tail_mem hzs hmem)
