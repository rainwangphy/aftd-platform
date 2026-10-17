import AFTD.Prelude
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSOp
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSCoords
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceInstAddCommGroupHSOp
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSIndex
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceInstModuleComplexHSOp
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceToHSCoordsLinearEquiv
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceToHSCoordsLinearEquivApplyApply
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceInstStarHSOp
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceInstMulHSOp
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceInstOneHSOp
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceInstInhabitedHSOp
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceInstZeroHSOp

/-!
# HilbertSchmidtOperatorSpace.instNormedAddCommGroupHSOp

Topic: quantum   Node: d509c96d88ec

Provenance: formalization of a published result. Source: QuantumInfo, `HilbertSchmidtOperatorSpace.instNormedAddCommGroupHSOp`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/HilbertSchmidtOperatorSpace.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HilbertSchmidtOperatorSpace.instNormedAddCommGroupHSOp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HilbertSchmidtOperatorSpace in
open LownerHeinzTheorem in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [FiniteDimensional ℂ ℋ] in
noncomputable instance HilbertSchmidtOperatorSpace.instNormedAddCommGroupHSOp : NormedAddCommGroup (HSOp ℋ) :=
  NormedAddCommGroup.induced (HSOp ℋ) (HSCoords ℋ)
    (toHSCoordsLinearEquiv (ℋ := ℋ)) (toHSCoordsLinearEquiv (ℋ := ℋ)).injective
