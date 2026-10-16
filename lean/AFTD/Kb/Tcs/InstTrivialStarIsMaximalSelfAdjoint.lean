import AFTD.Prelude
import AFTD.Kb.Tcs.IsMaximalSelfAdjoint

/-!
# instTrivialStarIsMaximalSelfAdjoint

Topic: quantum   Node: ebf1d25a390d

Provenance: formalization of a published result. Source: QuantumInfo, `instTrivialStarIsMaximalSelfAdjoint`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/IsMaximalSelfAdjoint.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Every `TrivialStar` `CommSemiring` is its own maximal self adjoints.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Every `TrivialStar` `CommSemiring` is its own maximal self adjoints. -/
instance instTrivialStarIsMaximalSelfAdjoint {R} [Star R] [TrivialStar R] [CommSemiring R] :
    IsMaximalSelfAdjoint R R where
  selfadjMap := AddMonoidHom.id R
  selfadj_smul _ __ := rfl
  selfadj_algebra {_} _ := rfl
