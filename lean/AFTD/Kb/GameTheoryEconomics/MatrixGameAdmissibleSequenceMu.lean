import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameAdmissibleSequence
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.AdmissibleSequence.mu

Topic: equilibria   Node: 1de84c4fd354

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.AdmissibleSequence.mu`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Learning/Robinson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cumulative duality gap `μ(t) := max_i β^i(t) - min_j α^j(t)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable {A : MatrixGame I J ℝ} in
/-- Cumulative duality gap `μ(t) := max_i β^i(t) - min_j α^j(t)`. -/
noncomputable def MatrixGame.AdmissibleSequence.mu (s : AdmissibleSequence A) (t : ℕ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (s.β t)
    - Finset.univ.inf' Finset.univ_nonempty (s.α t)
