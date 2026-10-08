import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisIsPositive
import AFTD.Kb.GameTheoryEconomics.LoomisXB
import AFTD.Kb.GameTheoryEconomics.LoomisXA
import AFTD.Kb.GameTheoryEconomics.LoomisAy
import AFTD.Kb.GameTheoryEconomics.LoomisBy
import AFTD.Kb.GameTheoryEconomics.LoomisLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisExistsXxLamB0
import AFTD.Kb.GameTheoryEconomics.LoomisMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisExistsYyMuB0
import AFTD.Kb.GameTheoryEconomics.LoomisLoomisValueEq
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.loomis_theorem

Topic: equilibria   Node: bbc602d6a7ef

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.loomis_theorem`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

**Loomis Theorem** [MFoGT, Theorem 2.5.1]. For any pair of matrices `A B : I → J → ℝ` with `B` entrywise positive, there exist mixed strategies `x : Δ(I)`, `y : Δ(J)` and a value `v : ℝ` such that for every column `j ∈ J` and every row `i ∈ I`, $$ v \cdot (xB)_j \le (xA)_j, \qquad (Ay)_i \le v \cdot (By)_i. $$ The common value `v = lamB0 A B = muB0 A B`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Loomis in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- **Loomis Theorem** [MFoGT, Theorem 2.5.1]. For any pair of matrices `A B : I → J → ℝ` with `B` entrywise positive, there exist mixed strategies `x : Δ(I)`, `y : Δ(J)` and a value `v : ℝ` such that for every column `j ∈ J` and every row `i ∈ I`, $$ v \cdot (xB)_j \le (xA)_j, \qquad (Ay)_i \le v \cdot (By)_i. $$ The common value `v = lamB0 A B = muB0 A B`. -/
theorem Loomis.loomis_theorem (A B : I → J → ℝ) (hB : IsPositive B) :
    ∃ (x : stdSimplex ℝ I) (y : stdSimplex ℝ J) (v : ℝ),
      (∀ j, v * xB B x j ≤ xA A x j) ∧
      (∀ i, Ay A y i ≤ v * By B y i) := by
  obtain ⟨x, Hx⟩ := exists_xx_lamB0 A B hB
  obtain ⟨y, Hy⟩ := exists_yy_muB0 A B hB
  refine ⟨x, y, lamB0 A B, Hx, fun i => ?_⟩
  rw [loomis_value_eq A B hB]
  exact Hy i
