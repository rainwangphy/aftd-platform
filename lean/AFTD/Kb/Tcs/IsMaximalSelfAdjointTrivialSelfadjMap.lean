import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaximalSelfAdjoint
import AFTD.Kb.Tcs.InstTrivialStarIsMaximalSelfAdjoint
import AFTD.Kb.Tcs.InstRCLikeIsMaximalSelfAdjoint

/-!
# IsMaximalSelfAdjoint.trivial_selfadjMap

Topic: quantum   Node: f080817e7b86

Provenance: formalization of a published result. Source: QuantumInfo, `IsMaximalSelfAdjoint.trivial_selfadjMap`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/IsMaximalSelfAdjoint.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IsMaximalSelfAdjoint.trivial_selfadjMap
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
@[simp]
theorem IsMaximalSelfAdjoint.trivial_selfadjMap {R} [Star R] [TrivialStar R] [CommSemiring R] :
    (selfadjMap : R →+ R) = .id R := by
  rfl
