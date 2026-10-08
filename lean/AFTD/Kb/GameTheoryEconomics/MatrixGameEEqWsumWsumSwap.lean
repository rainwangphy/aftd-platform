import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameE
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MatrixGameEEqWsumWsum
import AFTD.Kb.Optimization.WsumWsumComm
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.E_eq_wsum_wsum_swap

Topic: equilibria   Node: e5a8bb3ff349

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.E_eq_wsum_wsum_swap`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGameNash.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Helper: swap order of the iterated `wsum` in `A.E`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
universe u in
variable {I J : Type u} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- Helper: swap order of the iterated `wsum` in `A.E`. -/
theorem MatrixGame.E_eq_wsum_wsum_swap
    {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    (A : MatrixGame I J 𝕜) (x : stdSimplex 𝕜 I) (y : stdSimplex 𝕜 J) :
    A.E x y = wsum y (fun j => wsum x (fun i => A.g i j)) := by
  rw [E_eq_wsum_wsum, wsum_wsum_comm]
