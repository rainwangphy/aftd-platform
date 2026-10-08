import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisRowOffset
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisRowOffsetEqWsum
import AFTD.Kb.Optimization.WsumMix
import AFTD.Kb.Optimization.StdSimplexMixApply
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.rowOffset_mix

Topic: equilibria   Node: 96aa6d73fc3d

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.rowOffset_mix`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convex combination linearity for `rowOffset` in the simplex argument.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Convex combination linearity for `rowOffset` in the simplex argument. -/
theorem Loomis.rowOffset_mix (A B : I → J → ℝ) (mu : ℝ)
    (x y : stdSimplex ℝ J) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (i : I) :
    rowOffset A B mu (stdSimplex.mix t ht₀ ht₁ x y) i
      = t * rowOffset A B mu x i + (1 - t) * rowOffset A B mu y i := by
  simp only [rowOffset_eq_wsum]
  exact wsum_mix t ht₀ ht₁ x y _
