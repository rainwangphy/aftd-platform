import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameMaximin
import AFTD.Kb.GameTheoryEconomics.MatrixGameMinimax
import AFTD.Kb.GameTheoryEconomics.LoomisMinmaxFromGeneral
import AFTD.Kb.GameTheoryEconomics.MinimaxMinimax
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.minimax_theorem

Topic: equilibria   Node: d1b5886b7dde

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.minimax_theorem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Von Neumann's Minimax Theorem**: For any finite matrix game, maximin = minimax. [MSZ 5.11, von Neumann 1928] Proof: the general (positive-`B`) Loomis theorem specialised to `B = 𝟙`, exported as [`Loomis.minmax_from_general`] (compactness + continuity + strong induction on `|I| + |J|`). The field-generic minimax (any linearly ordered field, not just ℝ) is proved separately by von Neumann symmetrisation in [`Minimax.minimax`] — no compactness, no order completeness.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- **Von Neumann's Minimax Theorem**: For any finite matrix game, maximin = minimax. [MSZ 5.11, von Neumann 1928] Proof: the general (positive-`B`) Loomis theorem specialised to `B = 𝟙`, exported as [`Loomis.minmax_from_general`] (compactness + continuity + strong induction on `|I| + |J|`). The field-generic minimax (any linearly ordered field, not just ℝ) is proved separately by von Neumann symmetrisation in [`Minimax.minimax`] — no compactness, no order completeness. -/
theorem MatrixGame.minimax_theorem : A.maximin = A.minimax :=
  Loomis.minmax_from_general A.g
