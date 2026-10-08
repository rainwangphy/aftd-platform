import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.GameTreeIsNashEquilibrium
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeKuhnExistsNE
import AFTD.Kb.GameTheoryEconomics.GameTreeChildren
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.Tcs.G
import AFTD.Kb.GameTheoryEconomics.IsNashEquilibrium

/-!
# GameTree.zermelo_exists_pure_NE

Topic: equilibria   Node: 1ddd87608f04

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.zermelo_exists_pure_NE`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Pure root Nash existence for a finite two-player game on `ℚ`: the `Fin 2` / `ℚ` instance of `Kuhn_exists_NE`. Zero-sum is **not** needed.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Pure root Nash existence for a finite two-player game on `ℚ`: the `Fin 2` / `ℚ` instance of `Kuhn_exists_NE`. Zero-sum is **not** needed. -/
theorem GameTree.zermelo_exists_pure_NE (g : GameTree (Fin 2) ℚ) :
    ∃ σ : Strategy (Fin 2) ℚ, GameTree.IsNashEquilibrium σ g :=
  Kuhn_exists_NE g
