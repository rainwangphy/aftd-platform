import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaximalSelfAdjoint
import AFTD.Kb.Tcs.InstRCLikeIsMaximalSelfAdjoint
import AFTD.Kb.Tcs.IsMaximalSelfAdjointTrivialSelfadjMap
import AFTD.Kb.Tcs.InstTrivialStarIsMaximalSelfAdjoint

/-!
# IsMaximalSelfAdjoint.RCLike_selfadjMap

Topic: quantum   Node: 31487b2276e6

Provenance: formalization of a published result. Source: QuantumInfo, `IsMaximalSelfAdjoint.RCLike_selfadjMap`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/IsMaximalSelfAdjoint.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsMaximalSelfAdjoint.RCLike_selfadjMap
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
theorem IsMaximalSelfAdjoint.RCLike_selfadjMap {α : Type*} [RCLike α] : (selfadjMap : α →+ ℝ) = RCLike.re := by
  rfl
