import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPositiveAffineOf
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# IsPositiveAffineOf.trans

Topic: general_equilibrium   Node: 1efe19b6aa03

Provenance: formalization of a published result. Source: EconCSLib, `IsPositiveAffineOf.trans`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/AffineTransform.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positive affine transformation is transitive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Positive affine transformation is transitive. -/
theorem IsPositiveAffineOf.trans {u v w : X → 𝕜}
    (h₁ : IsPositiveAffineOf u v) (h₂ : IsPositiveAffineOf v w) :
    IsPositiveAffineOf u w := by
  obtain ⟨a₁, b₁, ha₁, hv⟩ := h₁
  obtain ⟨a₂, b₂, ha₂, hw⟩ := h₂
  exact ⟨a₂ * a₁, a₂ * b₁ + b₂, mul_pos ha₂ ha₁, fun x => by rw [hw, hv]; ring⟩
