import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL

/-!
# LownerHeinzTheorem.instCFCRealSelfAdjoint

Topic: quantum   Node: 8e238e10de74

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzTheorem.instCFCRealSelfAdjoint`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzTheorem.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzTheorem.instCFCRealSelfAdjoint
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LownerHeinzTheorem in
universe u v in
open CFC in
variable {ℋ : Type u} [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
set_option synthInstance.maxHeartbeats 80000 in
noncomputable instance LownerHeinzTheorem.instCFCRealSelfAdjoint :
    ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint := inferInstance
