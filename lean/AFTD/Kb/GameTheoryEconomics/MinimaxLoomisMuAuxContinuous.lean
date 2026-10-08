import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMuAux
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumContinuous
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxContinuous
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxContinuous

/-!
# MinimaxLoomis.mu.aux.continuous

Topic: equilibria   Node: 12253b159a06

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.mu.aux.continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`mu.aux A` is continuous as a function of the simplex point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `mu.aux A` is continuous as a function of the simplex point. -/
theorem MinimaxLoomis.mu.aux.continuous (A : I → J → ℝ) :
    Continuous (mu.aux A) := by
  refine Continuous.finset_sup'_apply Finset.univ_nonempty ?_
  intro i _
  exact wsum_continuous (fun j => A i j)
