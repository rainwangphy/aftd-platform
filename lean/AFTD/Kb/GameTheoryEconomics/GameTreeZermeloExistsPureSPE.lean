import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GameTreeKuhnExistsSPEOn
import AFTD.Kb.GameTheoryEconomics.GameTreeIsSubgamePerfectOn
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeOutcomeNode
import AFTD.Kb.GameTheoryEconomics.GameTree
import AFTD.Kb.GameTheoryEconomics.GameTreeStrategy
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.GameTreeValueLeaf
import AFTD.Kb.GameTheoryEconomics.GameTreeValueNode
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListNil
import AFTD.Kb.GameTheoryEconomics.GameTreeValueListCons

/-!
# GameTree.zermelo_exists_pure_SPE

Topic: equilibria   Node: dc06755ab986

Provenance: formalization of a published result. Source: EconCSLib, `GameTree.zermelo_exists_pure_SPE`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/ExtensiveGame/Zermelo.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pure root-scoped subgame-perfect existence for a finite two-player game on `ℚ`: the `Fin 2` / `ℚ` instance of `Kuhn_exists_SPE_on`. Zero-sum is **not** needed for existence; see `zermelo_determinacy` for the zero-sum refinement.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Pure root-scoped subgame-perfect existence for a finite two-player game on `ℚ`: the `Fin 2` / `ℚ` instance of `Kuhn_exists_SPE_on`. Zero-sum is **not** needed for existence; see `zermelo_determinacy` for the zero-sum refinement. -/
theorem GameTree.zermelo_exists_pure_SPE (g : GameTree (Fin 2) ℚ) :
    ∃ σ : Strategy (Fin 2) ℚ, IsSubgamePerfectOn σ g :=
  Kuhn_exists_SPE_on g
