import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPositiveAffineOf
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# IsPositiveAffineOf.refl

Topic: general_equilibrium   Node: c84d75d74d52

Provenance: formalization of a published result. Source: EconCSLib, `IsPositiveAffineOf.refl`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/AffineTransform.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positive affine transformation is reflexive (identity: a=1, b=0).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- Positive affine transformation is reflexive (identity: a=1, b=0). -/
theorem IsPositiveAffineOf.refl (u : X → 𝕜) : IsPositiveAffineOf u u :=
  ⟨1, 0, one_pos, fun x => by ring⟩
