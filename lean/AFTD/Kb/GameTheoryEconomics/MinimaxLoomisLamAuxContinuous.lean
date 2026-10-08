import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumContinuous
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.GameTheoryEconomics.LoomisLamBAuxContinuous
import AFTD.Kb.GameTheoryEconomics.LoomisMuBAuxContinuous

/-!
# MinimaxLoomis.lam.aux.continuous

Topic: equilibria   Node: 3a2b294446f9

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.lam.aux.continuous`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`lam.aux A` is continuous as a function of the simplex point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `lam.aux A` is continuous as a function of the simplex point. -/
theorem MinimaxLoomis.lam.aux.continuous (A : I → J → ℝ) :
    Continuous (lam.aux A) := by
  refine Continuous.finset_inf'_apply Finset.univ_nonempty ?_
  intro j _
  exact wsum_continuous (fun i => A i j)
