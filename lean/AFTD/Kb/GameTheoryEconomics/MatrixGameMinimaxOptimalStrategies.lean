import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisLam0
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExistsXxLam0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisMu0
import AFTD.Kb.GameTheoryEconomics.MinimaxLoomisExistsYyMu0
import AFTD.Kb.GameTheoryEconomics.LoomisMinmaxFromGeneral
import AFTD.Kb.Optimization.WsumPureApply
import AFTD.Kb.Tcs.G

/-!
# MatrixGame.minimax_optimal_strategies

Topic: equilibria   Node: b01809f22e56

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.minimax_optimal_strategies`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Existence of optimal mixed strategies: there exist mixed strategies `xx` for Player I and `yy` for Player II and a value `v` such that: - Player I guarantees at least `v`: `∀ j, E(xx, j) ≥ v` - Player II limits payoff to at most `v`: `∀ i, E(i, yy) ≤ v` [MSZ Theorem 5.11, LRS Theorem 2.3.1]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MatrixGame in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable (A : MatrixGame I J ℝ) in
/-- Existence of optimal mixed strategies: there exist mixed strategies `xx` for Player I and `yy` for Player II and a value `v` such that: - Player I guarantees at least `v`: `∀ j, E(xx, j) ≥ v` - Player II limits payoff to at most `v`: `∀ i, E(i, yy) ≤ v` [MSZ Theorem 5.11, LRS Theorem 2.3.1] -/
theorem MatrixGame.minimax_optimal_strategies :
    ∃ (xx : stdSimplex ℝ I) (yy : stdSimplex ℝ J) (v : ℝ),
      (∀ j : J, A.Ej xx j ≥ v) ∧
      (∀ i : I, A.Ei i yy ≤ v) := by
  obtain ⟨xx, Hxx⟩ := MinimaxLoomis.exists_xx_lam0 A.g
  obtain ⟨yy, Hyy⟩ := MinimaxLoomis.exists_yy_mu0 A.g
  refine ⟨xx, yy, MinimaxLoomis.lam0 A.g, ?_, ?_⟩
  · -- ∀ j, Ej xx j ≥ lam0 A.g
    intro j
    -- A.Ej xx j = wsum xx (fun i => A.g i j) by unfolding payoffAgainstColumn.
    have : A.Ej xx j = wsum xx (fun i => A.g i j) := rfl
    rw [this]; exact Hxx j
  · -- ∀ i, Ei i yy ≤ lam0 A.g  (using lam0 = mu0)
    intro i
    have : A.Ei i yy = wsum yy (fun j => A.g i j) := rfl
    rw [this, Loomis.minmax_from_general A.g]
    exact Hyy i
