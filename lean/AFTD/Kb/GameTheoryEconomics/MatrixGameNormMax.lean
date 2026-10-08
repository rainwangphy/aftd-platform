import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.normMax

Topic: equilibria   Node: ed4451da0fa7

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.normMax`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Learning/Robinson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`‖A‖ := max_{i,j} |A_{i,j}|`, the entrywise sup norm of the payoff matrix. Field-generic in the abstract, but the Robinson analysis is stated over `ℝ` (needed for the asymptotic `o(t)` formulation).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- `‖A‖ := max_{i,j} |A_{i,j}|`, the entrywise sup norm of the payoff matrix. Field-generic in the abstract, but the Robinson analysis is stated over `ℝ` (needed for the asymptotic `o(t)` formulation). -/
noncomputable def MatrixGame.normMax (A : MatrixGame I J ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun i : I => Finset.univ.sup' Finset.univ_nonempty (fun j : J => |A.g i j|))
