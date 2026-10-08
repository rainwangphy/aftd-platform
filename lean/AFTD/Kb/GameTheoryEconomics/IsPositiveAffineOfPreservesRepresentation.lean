import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPositiveAffineOf
import AFTD.Kb.GameTheoryEconomics.RepresentsPreference
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.IsPositiveAffineOfPreservesLe

/-!
# IsPositiveAffineOf.preserves_representation

Topic: general_equilibrium   Node: 5f0659e1ad48

Provenance: formalization of a published result. Source: EconCSLib, `IsPositiveAffineOf.preserves_representation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Foundation/Utility/AffineTransform.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `u` represents a preference, so does any positive affine transform. [MSZ 2.22]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {X 𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
/-- If `u` represents a preference, so does any positive affine transform. [MSZ 2.22] -/
theorem IsPositiveAffineOf.preserves_representation [Preorder X] {u v : X → 𝕜}
    (h : IsPositiveAffineOf u v) (hrep : RepresentsPreference u) :
    RepresentsPreference v where
  le_iff a b := by
    rw [← h.preserves_le]
    exact hrep.le_iff a b
