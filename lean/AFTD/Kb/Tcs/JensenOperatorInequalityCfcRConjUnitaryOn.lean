import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.LownerHeinzTheoremCfcR
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL

/-!
# JensenOperatorInequality.cfcR_conj_unitary_on

Topic: quantum   Node: db4db99b1194

Provenance: formalization of a published result. Source: QuantumInfo, `JensenOperatorInequality.cfcR_conj_unitary_on`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/JensenOperatorInequalityIImpIV.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

JensenOperatorInequality.cfcR_conj_unitary_on
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
open LownerHeinzTheorem in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
lemma JensenOperatorInequality.cfcR_conj_unitary_on (s : Set ℝ) (f : ℝ → ℝ) (hcont : ContinuousOn f s)
    {A : L ℋ} (hAs : spectrum ℝ A ⊆ s)
    (u : unitary (L ℋ)) (hA : IsSelfAdjoint A) :
    cfcR (ℋ := ℋ) f (star u * A * u) = star u * cfcR (ℋ := ℋ) f A * u := by
  let φ : L ℋ →⋆ₐ[ℝ] L ℋ := (Unitary.conjStarAlgAut ℝ (L ℋ) (star u)).toStarAlgHom
  have hφ : Continuous φ := by
    have h1 : Continuous (fun x : L ℋ => (star u : L ℋ) * x * (u : L ℋ)) := by
      fun_prop
    have hEq : (fun x : L ℋ => φ x) = (fun x : L ℋ => (star u : L ℋ) * x * (u : L ℋ)) := by
      funext x
      simp [φ, Unitary.conjStarAlgAut_apply, mul_assoc]
    simpa [hEq] using h1
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hcont.mono hAs)
    (hφ := hφ) (ha := hA) (hφa := hφA)
  simpa [φ, cfcR, Unitary.conjStarAlgAut_apply, mul_assoc] using hmap.symm
