import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsAffineUtility
import AFTD.Kb.GameTheoryEconomics.IsRiskNeutral
import AFTD.Kb.Optimization.Wsum
import AFTD.Kb.Optimization.WsumAdd
import AFTD.Kb.Optimization.WsumSmul
import AFTD.Kb.Optimization.WsumConst
import AFTD.Kb.Optimization.WsumPureApply

/-!
# IsAffineUtility.isRiskNeutral

Topic: general_equilibrium   Node: ce271678f602

Provenance: formalization of a published result. Source: EconCSLib, `IsAffineUtility.isRiskNeutral`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An affine utility function is risk neutral. [MSZ 2.27, easy direction]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
set_option linter.unusedSectionVars false in
/-- An affine utility function is risk neutral. [MSZ 2.27, easy direction] -/
theorem IsAffineUtility.isRiskNeutral {I : Type*} [Fintype I] {u : 𝕜 → 𝕜}
    (h : IsAffineUtility u) : IsRiskNeutral (I := I) u := by
  obtain ⟨a, b, hu⟩ := h
  intro p x
  -- Write u ∘ x as a • x + const b, then use wsum linearity lemmas.
  have hcomp : u ∘ x = a • x + (fun _ => b) := by
    funext i; simp [Function.comp, hu, Pi.smul_apply, smul_eq_mul]
  rw [hcomp, wsum_add, wsum_smul, wsum_const, hu]
