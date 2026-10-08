import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLamAux
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumPureApply

/-!
# MinimaxLoomis.lam.aux_gt_iff_gt

Topic: equilibria   Node: 1e6c9a8d6cd2

Provenance: formalization of a published result. Source: EconCSLib, `MinimaxLoomis.lam.aux_gt_iff_gt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/MinimaxLoomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`lam.aux A x > c` iff every pure-column expected payoff exceeds `c`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `lam.aux A x > c` iff every pure-column expected payoff exceeds `c`. -/
theorem MinimaxLoomis.lam.aux_gt_iff_gt (A : I → J → ℝ) (c : ℝ) (x : stdSimplex ℝ I) :
    c < lam.aux A x ↔ ∀ j, c < wsum x (fun i => A i j) := by
  simp [lam.aux, Finset.lt_inf'_iff]
