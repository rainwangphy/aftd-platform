import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LoomisColOffset
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.GameTheoryEconomics.LoomisColOffsetEqWsum
import AFTD.Kb.Optimization.WsumMix
import AFTD.Kb.Optimization.StdSimplexMixApply
import AFTD.Kb.Optimization.WsumPureApply

/-!
# Loomis.colOffset_mix

Topic: equilibria   Node: f4442d5402f4

Provenance: formalization of a published result. Source: EconCSLib, `Loomis.colOffset_mix`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Minimax/Loomis.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Convex combination linearity for `colOffset` in the simplex argument.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators in
set_option linter.unusedSectionVars false in
variable {I J : Type*} [Fintype I] [Fintype J] [Nonempty I] [Nonempty J] in
/-- Convex combination linearity for `colOffset` in the simplex argument. -/
theorem Loomis.colOffset_mix (A B : I → J → ℝ) (lam : ℝ)
    (x y : stdSimplex ℝ I) (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (j : J) :
    colOffset A B lam (stdSimplex.mix t ht₀ ht₁ x y) j
      = t * colOffset A B lam x j + (1 - t) * colOffset A B lam y j := by
  simp only [colOffset_eq_wsum]
  exact wsum_mix t ht₀ ht₁ x y _
