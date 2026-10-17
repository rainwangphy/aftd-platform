import AFTD.Prelude
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSCoords
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSCoordFun
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSIndex

/-!
# HilbertSchmidtOperatorSpace.hsCoordsLinearEquiv

Topic: quantum   Node: 6f84b2245927

Provenance: formalization of a published result. Source: QuantumInfo, `HilbertSchmidtOperatorSpace.hsCoordsLinearEquiv`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/HilbertSchmidtOperatorSpace.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HilbertSchmidtOperatorSpace.hsCoordsLinearEquiv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HilbertSchmidtOperatorSpace in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [FiniteDimensional ℂ ℋ] in
noncomputable def HilbertSchmidtOperatorSpace.hsCoordsLinearEquiv :
    HSCoords ℋ ≃ₗ[ℂ] (HSCoordFun ℋ) := by
  simpa [HSCoords, HSCoordFun] using
    (WithLp.linearEquiv (2 : ENNReal) ℂ (HSCoordFun ℋ))
