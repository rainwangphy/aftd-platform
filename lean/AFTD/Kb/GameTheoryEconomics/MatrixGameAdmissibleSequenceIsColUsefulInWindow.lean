import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameAdmissibleSequence
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstDecidableEqStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstFintypeStrategyFinOfNatNatToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameInstNonemptyStrategyFinOfNatNatToStrategicGame

/-!
# MatrixGame.AdmissibleSequence.IsColUsefulInWindow

Topic: equilibria   Node: a92be3dfbf8c

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.AdmissibleSequence.IsColUsefulInWindow`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/Learning/Robinson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A pure column `j` is **useful** in the window `[s, s + t*]` analogously.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable {A : MatrixGame I J ℝ} in
/-- A pure column `j` is **useful** in the window `[s, s + t*]` analogously. -/
def MatrixGame.AdmissibleSequence.IsColUsefulInWindow (s : AdmissibleSequence A) (start length : ℕ) (j : J) : Prop :=
  ∃ k, start ≤ k ∧ k < start + length ∧ s.jSeq k = j
