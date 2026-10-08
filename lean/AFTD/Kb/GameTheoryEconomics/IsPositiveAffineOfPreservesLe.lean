import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPositiveAffineOf
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# IsPositiveAffineOf.preserves_le

Topic: general_equilibrium   Node: 6aeb810d44f8

Provenance: formalization of a published result. Source: EconCSLib, `IsPositiveAffineOf.preserves_le`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/AffineTransform.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A positive affine transform preserves the order: `u x ≤ u y ↔ v x ≤ v y`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- A positive affine transform preserves the order: `u x ≤ u y ↔ v x ≤ v y`. -/
theorem IsPositiveAffineOf.preserves_le {u v : X → 𝕜}
    (h : IsPositiveAffineOf u v) (x y : X) :
    u x ≤ u y ↔ v x ≤ v y := by
  obtain ⟨a, b, ha, hv⟩ := h
  simp only [hv]
  constructor
  · intro hle
    have := mul_le_mul_of_nonneg_left hle (le_of_lt ha)
    linarith
  · intro hle
    have : a * u x + b ≤ a * u y + b := hle
    have : a * u x ≤ a * u y := by linarith
    exact le_of_mul_le_mul_left this ha
