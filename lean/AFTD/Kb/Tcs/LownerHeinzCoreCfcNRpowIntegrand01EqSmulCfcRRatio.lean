import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# LownerHeinzCore.cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio

Topic: quantum   Node: 1a8bef3d93bd

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzCore.cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzCore.cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LownerHeinzCore in
universe u v in
open CFC in
variable {𝓐 : Type u} in
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] in
variable [Nontrivial 𝓐] in
variable [NonnegSpectrumClass ℝ 𝓐] in
omit [Nontrivial (𝓐)] in
omit [StarOrderedRing 𝓐] in
lemma LownerHeinzCore.cfcₙ_rpowIntegrand₀₁_eq_smul_cfcR_ratio {q : NNReal} (hq : q ∈ Set.Ioo (0 : NNReal) 1)
    {t : ℝ} (htpos : 0 < t) (X : 𝓐) (hX0 : 0 ≤ X) :
    cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
      (t ^ ((q : ℝ) - 1)) • cfcR (fun x : ℝ => x / (x + t)) X := by
  have hq_real : ((q : ℝ) : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := ⟨(NNReal.coe_pos).2 hq.1, (NNReal.coe_lt_coe).2 hq.2⟩
  let ratio : ℝ → ℝ := fun x => x / (x + t)
  let r : ℝ := t ^ ((q : ℝ) - 1)
  have hcont_ratio : ContinuousOn ratio (spectrum ℝ X) :=
    continuousOn_id.div (continuousOn_id.add continuousOn_const) (fun x hx ↦ ne_of_gt (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg hX0 hx) htpos))
  have hcfcₙ : cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
      cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X := by
    have hqs : quasispectrum ℝ X ⊆ Set.Ici (0 : ℝ) := by
      intro x hx
      have hx0 : (0 : ℝ) ≤ x := quasispectrum_nonneg_of_nonneg X hX0 x hx
      simpa [Set.Ici] using hx0
    have hf : ContinuousOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (quasispectrum ℝ X) :=
      (Real.continuousOn_rpowIntegrand₀₁_Ici hq_real htpos).mono hqs
    simpa using
      (cfcₙ_eq_cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := Real.rpowIntegrand₀₁ (q : ℝ) t) (a := X) (hf := hf) (hf0 := by simp))
  have hEq :
      (spectrum ℝ X).EqOn (Real.rpowIntegrand₀₁ (q : ℝ) t) (fun x : ℝ ↦ r * ratio x) := by
    intro x hx
    simp [r, ratio, Real.rpowIntegrand₀₁_eq_pow_div hq_real (le_of_lt htpos) (spectrum_nonneg_of_nonneg hX0 hx),
      add_comm, mul_div_assoc]
  have hcfc_congr :
      cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
        cfcR (fun x : ℝ ↦ r * ratio x) X :=
    cfc_congr hEq
  have hcfc_mul :
      cfcR (fun x : ℝ ↦ r * ratio x) X =
        r • cfcR ratio X := by
    simpa using
      (cfc_const_mul (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := r) (f := ratio) (a := X)
        (hf := hcont_ratio))
  have hmain :
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X = r • cfcR ratio X := by
    calc
      cfcₙ (Real.rpowIntegrand₀₁ (q : ℝ) t) X =
          cfcR (Real.rpowIntegrand₀₁ (q : ℝ) t) X := by
            simpa using hcfcₙ
      _ = cfcR (fun x : ℝ ↦ r * ratio x) X := hcfc_congr
      _ = r • cfcR ratio X := hcfc_mul
      _ = r • cfcR ratio X := by simp [cfcR]
  simpa [r, ratio] using hmain
