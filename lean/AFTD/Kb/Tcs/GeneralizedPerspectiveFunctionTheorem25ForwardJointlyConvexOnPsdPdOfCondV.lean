import AFTD.Prelude
import AFTD.Kb.Tcs.JensenOperatorInequalityCondV
import AFTD.Kb.Tcs.LownerHeinzTheoremOperatorConcaveOn
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionJointlyConvexOn
import AFTD.Kb.Tcs.LownerHeinzTheoremL
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionPsdSet
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionPdSet
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionGeneralizedPerspective
import AFTD.Kb.Tcs.LownerHeinzTheoremInstCFCRealSelfAdjoint
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionSpectrumConvexComboIoi
import AFTD.Kb.Tcs.LownerHeinzTheoremCfcR
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHSqrt
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHInvSqrt
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHSqrtSelfAdjoint
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHInvSqrtSelfAdjoint
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHSqrtMulHInvSqrtEqOne
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHInvSqrtMulHSqrtEqOne
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionHSqrtMulHSqrtEq
import AFTD.Kb.Tcs.GeneralizedPerspectiveFunctionConjLeConj
import AFTD.Kb.Tcs.LownerHeinzTheoremOperatorConvexOn
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalStar
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockDiagonalHomApply
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockDiagonalOne
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpZero
import AFTD.Kb.Tcs.JensenOperatorInequalityHsumProjBlockOpOne
import AFTD.Kb.Tcs.JensenOperatorInequalityBlockOpStar
import AFTD.Kb.Tcs.LownerHeinzTheoremInstNontrivialL
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointSmul

/-!
# GeneralizedPerspectiveFunction.theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV

Topic: quantum   Node: 1361e8d5de80

Provenance: formalization of a published result. Source: QuantumInfo, `GeneralizedPerspectiveFunction.theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/GeneralizedPerspectiveFunction.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

GeneralizedPerspectiveFunction.theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV
-/

set_option quotPrecheck false
open GeneralizedPerspectiveFunction
local infixl:70 " Δ " => GeneralizedPerspective

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open GeneralizedPerspectiveFunction in
universe u in
open LownerHeinzTheorem in
open JensenOperatorInequality in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [Nontrivial ℋ] in
set_option maxHeartbeats 800000 in
-- The generalized-perspective normalization expands several nested CFC products.
theorem GeneralizedPerspectiveFunction.theorem_2_5_forward_jointlyConvexOn_psd_pd_of_condV
    {f h : ℝ → ℝ}
    (hcoreV : CondV (ℋ := ℋ) f)
    (hconc : OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) h)
    (hcont : ContinuousOn h (Set.Ioi (0 : ℝ)))
    (hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 < h x) :
    JointlyConvexOn (psdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ)) (fun A B ↦ (f Δ h) A B) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  rcases hA₁ with ⟨hA₁_sa, hA₁_spec⟩
  rcases hA₂ with ⟨hA₂_sa, hA₂_spec⟩
  rcases hB₁ with ⟨hB₁_sa, hB₁_spec⟩
  rcases hB₂ with ⟨hB₂_sa, hB₂_spec⟩
  let A : L ℋ := (1 - θ) • A₁ + θ • A₂
  let B : L ℋ := (1 - θ) • B₁ + θ • B₂
  have hA₁_nonneg : (0 : L ℋ) ≤ A₁ := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A₁ (ha := hA₁_sa)).2 ?_
    intro x hx
    simpa [Set.Ici] using hA₁_spec hx
  have hA₂_nonneg : (0 : L ℋ) ≤ A₂ := by
    refine (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A₂ (ha := hA₂_sa)).2 ?_
    intro x hx
    simpa [Set.Ici] using hA₂_spec hx
  have hB_sa : IsSelfAdjoint B := by
    dsimp [B]
    simpa using (IsSelfAdjoint.all (1 - θ)).smul hB₁_sa |>.add ((IsSelfAdjoint.all θ).smul hB₂_sa)
  have hB_spec : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ) :=
    spectrum_convexCombo_Ioi (ℋ := ℋ) hB₁_sa hB₂_sa hθ0 hθ1 hB₁_spec hB₂_spec
  have hB_conc :
      (1 - θ) • cfcR (ℋ := ℋ) h B₁ + θ • cfcR (ℋ := ℋ) h B₂ ≤ cfcR (ℋ := ℋ) h B := by
    have hconc' := hconc
    dsimp [OperatorConcaveOn, OperatorConvexOn] at hconc'
    have hneg :
        cfcR (ℋ := ℋ) (fun x : ℝ ↦ -h x) B ≤
          (1 - θ) • cfcR (ℋ := ℋ) (fun x : ℝ ↦ -h x) B₁ +
            θ • cfcR (ℋ := ℋ) (fun x : ℝ ↦ -h x) B₂ := by
      simpa [B] using
        hconc' (A := B₁) (B := B₂) (t := θ) hB₁_sa hB₂_sa hθ0 hθ1 hB₁_spec hB₂_spec
    simpa [cfcR, cfc_neg, smul_neg, neg_add, add_comm, add_left_comm, add_assoc] using
      neg_le_neg hneg
  let S : L ℋ := hSqrt (ℋ := ℋ) h B
  let IR : L ℋ := hInvSqrt (ℋ := ℋ) h B
  let S₁ : L ℋ := hSqrt (ℋ := ℋ) h B₁
  let S₂ : L ℋ := hSqrt (ℋ := ℋ) h B₂
  let IR₁ : L ℋ := hInvSqrt (ℋ := ℋ) h B₁
  let IR₂ : L ℋ := hInvSqrt (ℋ := ℋ) h B₂
  let T₁ : L ℋ := Real.sqrt (1 - θ) • (S₁ * IR)
  let T₂ : L ℋ := Real.sqrt θ • (S₂ * IR)
  let M₁ : L ℋ := IR₁ * A₁ * IR₁
  let M₂ : L ℋ := IR₂ * A₂ * IR₂
  have hS_sa : IsSelfAdjoint S := hSqrt_selfAdjoint (ℋ := ℋ) h B
  have hIR_sa : IsSelfAdjoint IR := hInvSqrt_selfAdjoint (ℋ := ℋ) h B
  have hS₁_sa : IsSelfAdjoint S₁ := hSqrt_selfAdjoint (ℋ := ℋ) h B₁
  have hS₂_sa : IsSelfAdjoint S₂ := hSqrt_selfAdjoint (ℋ := ℋ) h B₂
  have hIR₁_sa : IsSelfAdjoint IR₁ := hInvSqrt_selfAdjoint (ℋ := ℋ) h B₁
  have hIR₂_sa : IsSelfAdjoint IR₂ := hInvSqrt_selfAdjoint (ℋ := ℋ) h B₂
  have hSIR : S * IR = (1 : L ℋ) :=
    hSqrt_mul_hInvSqrt_eq_one (ℋ := ℋ) hB_sa hB_spec hcont hpos
  have hIRS : IR * S = (1 : L ℋ) :=
    hInvSqrt_mul_hSqrt_eq_one (ℋ := ℋ) hB_sa hB_spec hcont hpos
  have hS₁IR₁ : S₁ * IR₁ = (1 : L ℋ) :=
    hSqrt_mul_hInvSqrt_eq_one (ℋ := ℋ) hB₁_sa hB₁_spec hcont hpos
  have hIR₁S₁ : IR₁ * S₁ = (1 : L ℋ) :=
    hInvSqrt_mul_hSqrt_eq_one (ℋ := ℋ) hB₁_sa hB₁_spec hcont hpos
  have hS₂IR₂ : S₂ * IR₂ = (1 : L ℋ) :=
    hSqrt_mul_hInvSqrt_eq_one (ℋ := ℋ) hB₂_sa hB₂_spec hcont hpos
  have hIR₂S₂ : IR₂ * S₂ = (1 : L ℋ) :=
    hInvSqrt_mul_hSqrt_eq_one (ℋ := ℋ) hB₂_sa hB₂_spec hcont hpos
  have hM₁_nonneg : (0 : L ℋ) ≤ M₁ := by
    dsimp [M₁]
    simpa [mul_assoc] using hIR₁_sa.conjugate_nonneg hA₁_nonneg
  have hM₂_nonneg : (0 : L ℋ) ≤ M₂ := by
    dsimp [M₂]
    simpa [mul_assoc] using hIR₂_sa.conjugate_nonneg hA₂_nonneg
  have hM₁_sa : IsSelfAdjoint M₁ := IsSelfAdjoint.of_nonneg hM₁_nonneg
  have hM₂_sa : IsSelfAdjoint M₂ := IsSelfAdjoint.of_nonneg hM₂_nonneg
  have hM₁_spec : spectrum ℝ M₁ ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    simpa [Set.Ici] using spectrum_nonneg_of_nonneg hM₁_nonneg hx
  have hM₂_spec : spectrum ℝ M₂ ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    simpa [Set.Ici] using spectrum_nonneg_of_nonneg hM₂_nonneg hx
  have hT₁ :
      star T₁ * T₁ = (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) := by
    calc
      star T₁ * T₁
          = (Real.sqrt (1 - θ) * Real.sqrt (1 - θ)) • (IR * (S₁ * S₁) * IR) := by
              simp [T₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (IR * (S₁ * S₁) * IR) := by
              rw [Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
      _ = (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) := by
              rw [hSqrt_mul_hSqrt_eq (ℋ := ℋ) (B := B₁) hB₁_spec hcont hpos]
  have hT₂ :
      star T₂ * T₂ = θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR) := by
    calc
      star T₂ * T₂
          = (Real.sqrt θ * Real.sqrt θ) • (IR * (S₂ * S₂) * IR) := by
              simp [T₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (IR * (S₂ * S₂) * IR) := by
              rw [Real.mul_self_sqrt hθ0]
      _ = θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR) := by
              rw [hSqrt_mul_hSqrt_eq (ℋ := ℋ) (B := B₂) hB₂_spec hcont hpos]
  have hTsum : star T₁ * T₁ + star T₂ * T₂ ≤ (1 : L ℋ) := by
    rw [hT₁, hT₂]
    have hmid :
        (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) + θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR)
          ≤ IR * cfcR (ℋ := ℋ) h B * IR := by
      calc
        (1 - θ) • (IR * cfcR (ℋ := ℋ) h B₁ * IR) + θ • (IR * cfcR (ℋ := ℋ) h B₂ * IR)
            = IR * ((1 - θ) • cfcR (ℋ := ℋ) h B₁ + θ • cfcR (ℋ := ℋ) h B₂) * IR := by
                simp [mul_add, add_mul, mul_assoc]
        _ ≤ IR * cfcR (ℋ := ℋ) h B * IR := conj_le_conj (ℋ := ℋ) hB_conc hIR_sa
    have hunit : IR * cfcR (ℋ := ℋ) h B * IR = (1 : L ℋ) := by
      calc
        IR * cfcR (ℋ := ℋ) h B * IR = IR * (S * S) * IR := by
          rw [hSqrt_mul_hSqrt_eq (ℋ := ℋ) (B := B) hB_spec hcont hpos]
        _ = (IR * S) * (S * IR) := by simp [mul_assoc]
        _ = 1 := by simp [hIRS, hSIR]
    exact hmid.trans_eq hunit
  have hterm₁ :
      star T₁ * M₁ * T₁ = (1 - θ) • (IR * A₁ * IR) := by
    calc
      star T₁ * M₁ * T₁
          = (Real.sqrt (1 - θ) * Real.sqrt (1 - θ)) •
              (IR * (S₁ * (IR₁ * A₁ * IR₁) * S₁) * IR) := by
                simp [T₁, M₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (IR * (S₁ * (IR₁ * A₁ * IR₁) * S₁) * IR) := by
            rw [Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
      _ = (1 - θ) • (IR * A₁ * IR) := by
            rw [show IR * (S₁ * (IR₁ * A₁ * IR₁) * S₁) * IR =
                IR * (((S₁ * IR₁) * A₁) * (IR₁ * S₁)) * IR by simp [mul_assoc]]
            rw [hS₁IR₁, hIR₁S₁]
            simp [mul_assoc]
  have hterm₂ :
      star T₂ * M₂ * T₂ = θ • (IR * A₂ * IR) := by
    calc
      star T₂ * M₂ * T₂
          = (Real.sqrt θ * Real.sqrt θ) •
              (IR * (S₂ * (IR₂ * A₂ * IR₂) * S₂) * IR) := by
                simp [T₂, M₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (IR * (S₂ * (IR₂ * A₂ * IR₂) * S₂) * IR) := by
            rw [Real.mul_self_sqrt hθ0]
      _ = θ • (IR * A₂ * IR) := by
            rw [show IR * (S₂ * (IR₂ * A₂ * IR₂) * S₂) * IR =
                IR * (((S₂ * IR₂) * A₂) * (IR₂ * S₂)) * IR by simp [mul_assoc]]
            rw [hS₂IR₂, hIR₂S₂]
            simp [mul_assoc]
  have hleft_inner :
      star T₁ * M₁ * T₁ + star T₂ * M₂ * T₂ = IR * A * IR := by
    rw [hterm₁, hterm₂]
    simp [A, mul_add, add_mul, mul_assoc]
  have hcore :=
    hcoreV (A := M₁) (B := M₂) (X := T₁) (Y := T₂) hM₁_sa hM₂_sa hM₁_spec hM₂_spec hTsum
  have houter := conj_le_conj (ℋ := ℋ) hcore hS_sa
  rw [hleft_inner] at houter
  have hright₁ :
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁) * S =
        (1 - θ) • ((f Δ h) A₁ B₁) := by
    calc
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁) * S
          = (Real.sqrt (1 - θ) * Real.sqrt (1 - θ)) •
              (S * IR * (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) * IR * S) := by
                simp [T₁, hS₁_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = (1 - θ) • (S * IR * (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) * IR * S) := by
            rw [Real.mul_self_sqrt (sub_nonneg.mpr hθ1)]
      _ = (1 - θ) • (S₁ * cfcR (ℋ := ℋ) f M₁ * S₁) := by
            simp [mul_assoc, hSIR, hIRS]
      _ = (1 - θ) • ((f Δ h) A₁ B₁) := by
            rfl
  have hright₂ :
      S * (star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S =
        θ • ((f Δ h) A₂ B₂) := by
    calc
      S * (star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S
          = (Real.sqrt θ * Real.sqrt θ) •
              (S * IR * (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) * IR * S) := by
                simp [T₂, hS₂_sa.star_eq, hIR_sa.star_eq, mul_assoc, smul_smul]
      _ = θ • (S * IR * (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) * IR * S) := by
            rw [Real.mul_self_sqrt hθ0]
      _ = θ • (S₂ * cfcR (ℋ := ℋ) f M₂ * S₂) := by
            simp [mul_assoc, hSIR, hIRS]
      _ = θ • ((f Δ h) A₂ B₂) := by
            rfl
  have hright :
      S * (star T₁ * cfcR (ℋ := ℋ) f M₁ * T₁ + star T₂ * cfcR (ℋ := ℋ) f M₂ * T₂) * S =
        (1 - θ) • ((f Δ h) A₁ B₁) + θ • ((f Δ h) A₂ B₂) := by
    rw [mul_add, add_mul, hright₁, hright₂]
  have hleft :
      S * cfcR (ℋ := ℋ) f (IR * A * IR) * S = (f Δ h) A B := by
    rfl
  simpa [hleft, hright] using houter

-- Restricted forward form of Theorem 2.5 on the positive cone.
