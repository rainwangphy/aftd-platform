import AFTD.Prelude
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.StdSimplexMix
import AFTD.Kb.Optimization.WsumMix
import AFTD.Kb.Optimization.LinearCombLtOfLeLt
import AFTD.Kb.Optimization.StdSimplexMixApply

/-!
# wsum_mix_lt_of_le_lt

Topic: lp_duality   Node: 693403b673ce

Provenance: formalization of a published result. Source: EconCSLib, `wsum_mix_lt_of_le_lt`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/Simplex.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`wsum` version of `linear_comb_lt_of_le_lt`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
variable {I : Type*} [Fintype I] in
set_option linter.unusedSectionVars false in
/-- `wsum` version of `linear_comb_lt_of_le_lt`. -/
theorem wsum_mix_lt_of_le_lt {I : Type*} [Fintype I]
    (f : I → 𝕜) (x y : stdSimplex 𝕜 I) (c : 𝕜)
    (H1 : wsum x f ≤ c) (H2 : wsum y f < c)
    {t : 𝕜} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) (Ht : t < 1) :
    wsum (stdSimplex.mix t ht₀ ht₁ x y) f < c := by
  rw [wsum_mix]
  exact linear_comb_lt_of_le_lt _ _ c H1 H2 ht₀ Ht
