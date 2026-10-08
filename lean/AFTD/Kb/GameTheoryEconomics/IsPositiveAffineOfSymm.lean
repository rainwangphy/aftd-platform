import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPositiveAffineOf
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# IsPositiveAffineOf.symm

Topic: general_equilibrium   Node: c9e5b69d2b34

Provenance: formalization of a published result. Source: EconCSLib, `IsPositiveAffineOf.symm`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/AffineTransform.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positive affine transformation is symmetric (invertible). [MSZ Ex 2.19] If `v(x) = a·u(x) + b` with `a > 0`, then `u(x) = (1/a)·v(x) + (-b/a)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Positive affine transformation is symmetric (invertible). [MSZ Ex 2.19] If `v(x) = a·u(x) + b` with `a > 0`, then `u(x) = (1/a)·v(x) + (-b/a)`. -/
theorem IsPositiveAffineOf.symm {u v : X → 𝕜}
    (h : IsPositiveAffineOf u v) : IsPositiveAffineOf v u := by
  obtain ⟨a, b, ha, hv⟩ := h
  exact ⟨1/a, -b/a, div_pos one_pos ha, fun x => by
    have ha' : a ≠ 0 := ne_of_gt ha
    field_simp [ha']; linarith [hv x]⟩
