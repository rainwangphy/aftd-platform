import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaximalSelfAdjoint
import AFTD.Kb.Tcs.InstTrivialStarIsMaximalSelfAdjoint

/-!
# instRCLikeIsMaximalSelfAdjoint

Topic: quantum   Node: 4387d5b91348

Provenance: formalization of a published result. Source: QuantumInfo, `instRCLikeIsMaximalSelfAdjoint`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/IsMaximalSelfAdjoint.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 adapted; compiled here.

ℝ is the maximal self adjoint elements over RCLike
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- ℝ is the maximal self adjoint elements over RCLike -/
instance instRCLikeIsMaximalSelfAdjoint {α : Type*} [RCLike α] : IsMaximalSelfAdjoint ℝ α where
  selfadjMap := RCLike.re
  selfadj_smul := RCLike.smul_re
  selfadj_algebra := RCLike.conj_eq_iff_re.mp
