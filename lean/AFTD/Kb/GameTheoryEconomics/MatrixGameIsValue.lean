import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MatrixGame
import AFTD.Kb.GameTheoryEconomics.MatrixGameEj
import AFTD.Kb.GameTheoryEconomics.MatrixGameEi
import AFTD.Kb.GameTheoryEconomics.MatrixGameValue

/-!
# MatrixGame.IsValue

Topic: equilibria   Node: 8a27f2df0a7b

Provenance: formalization of a published result. Source: EconCSLib, `MatrixGame.IsValue`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/GameTheory/StrategicGame/ZeroSum/MatrixGame.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`v` is **the value** of `A` (saddle-point form): there exist a row mixed strategy `x` and column mixed strategy `y` such that `x` guarantees at least `v` against every column and `y` caps player I's payoff at `v` against every row. Field-generic; `MatrixGame.value` below is the ℝ-valued specialisation (via `iSup`) when `𝕜` admits order completeness.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
variable {𝕜 : Type} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable (A : MatrixGame I J 𝕜) in
/-- `v` is **the value** of `A` (saddle-point form): there exist a row mixed strategy `x` and column mixed strategy `y` such that `x` guarantees at least `v` against every column and `y` caps player I's payoff at `v` against every row. Field-generic; `MatrixGame.value` below is the ℝ-valued specialisation (via `iSup`) when `𝕜` admits order completeness. -/
def MatrixGame.IsValue (A : MatrixGame I J 𝕜) (v : 𝕜) : Prop :=
  ∃ x : stdSimplex 𝕜 I, ∃ y : stdSimplex 𝕜 J,
    (∀ j, v ≤ A.Ej x j) ∧ (∀ i, A.Ei i y ≤ v)
