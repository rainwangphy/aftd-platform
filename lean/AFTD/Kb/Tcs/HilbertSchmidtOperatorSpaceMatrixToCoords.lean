import AFTD.Prelude
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSIndex
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSCoords
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSCoordFun
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceMatrixToFun
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHsCoordsLinearEquiv

/-!
# HilbertSchmidtOperatorSpace.matrixToCoords

Topic: quantum   Node: 4224f18bad18

Provenance: formalization of a published result. Source: QuantumInfo, `HilbertSchmidtOperatorSpace.matrixToCoords`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/HilbertSchmidtOperatorSpace.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HilbertSchmidtOperatorSpace.matrixToCoords
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HilbertSchmidtOperatorSpace in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [FiniteDimensional ℂ ℋ] in
noncomputable def HilbertSchmidtOperatorSpace.matrixToCoords :
    Matrix (HSIndex ℋ) (HSIndex ℋ) ℂ ≃ₗ[ℂ] HSCoords ℋ :=
  (matrixToFun (ℋ := ℋ)).trans hsCoordsLinearEquiv.symm
