import AFTD.Prelude
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSOp
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceInstAddCommGroupHSOp

/-!
# HilbertSchmidtOperatorSpace.instStarHSOp

Topic: quantum   Node: 3e80ba3e1020

Provenance: formalization of a published result. Source: QuantumInfo, `HilbertSchmidtOperatorSpace.instStarHSOp`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/HilbertSchmidtOperatorSpace.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HilbertSchmidtOperatorSpace.instStarHSOp
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HilbertSchmidtOperatorSpace in
open LownerHeinzTheorem in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [FiniteDimensional ℂ ℋ] in
noncomputable instance HilbertSchmidtOperatorSpace.instStarHSOp : Star (HSOp ℋ) := by
  delta HSOp
  infer_instance
