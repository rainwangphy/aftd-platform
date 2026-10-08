import AFTD.Prelude

/-!
# BayesianSingleItemAuction.survivalIntegral_eq_intervalIntegral_mul_deriv

Topic: mechanism_design   Node: ac3a50e240d0

Provenance: formalization of a published result. Source: EconCSLib, `BayesianSingleItemAuction.survivalIntegral_eq_intervalIntegral_mul_deriv`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/OptimalSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Integration by parts for the survival term.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
open MeasureTheory in
variable {I : Type*} in
/-- Integration by parts for the survival term. -/
theorem BayesianSingleItemAuction.survivalIntegral_eq_intervalIntegral_mul_deriv
    {F Q : ℝ → ℝ} {ω : ℝ}
    (hω : 0 ≤ ω)
    (hF : AbsolutelyContinuousOnInterval F 0 ω)
    (hF0 : F 0 = 0) (hFω : F ω = 1)
    (hQ : IntervalIntegrable Q volume 0 ω) :
    (∫ v in 0..ω, Q v * (1 - F v)) =
      ∫ v in 0..ω, (∫ z in 0..v, Q z) * deriv F v := by
  let G : ℝ → ℝ := fun v => ∫ z in 0..v, Q z
  have h0mem : (0 : ℝ) ∈ Set.uIcc 0 ω := by
    rw [Set.uIcc_of_le hω]
    exact ⟨le_rfl, hω⟩
  have hG : AbsolutelyContinuousOnInterval G 0 ω :=
    hQ.absolutelyContinuousOnInterval_intervalIntegral h0mem
  have hQF : IntervalIntegrable (fun v => Q v * F v) volume 0 ω :=
    by simpa [mul_comm] using hQ.continuousOn_mul hF.continuousOn
  have hderiv_ae :
      ∀ᵐ v ∂volume, v ∈ Set.uIoc 0 ω → deriv G v = Q v := by
    filter_upwards [hQ.ae_hasDerivAt_integral] with v hv hv_mem
    exact (hv (Set.uIoc_subset_uIcc hv_mem) 0 h0mem).deriv
  have hderiv_integral :
      (∫ v in 0..ω, deriv G v * F v) =
        ∫ v in 0..ω, Q v * F v := by
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [hderiv_ae] with v hv hv_mem
    rw [hv hv_mem]
  have hibp :
      (∫ v in 0..ω, G v * deriv F v) =
        (∫ v in 0..ω, Q v) - ∫ v in 0..ω, Q v * F v := by
    calc
      (∫ v in 0..ω, G v * deriv F v)
          = G ω * F ω - G 0 * F 0 - ∫ v in 0..ω, deriv G v * F v :=
            hG.integral_mul_deriv_eq_deriv_mul hF
      _ = (∫ v in 0..ω, Q v) - ∫ v in 0..ω, Q v * F v := by
            rw [hderiv_integral]
            simp [G, hF0, hFω]
  have hsurvival :
      (∫ v in 0..ω, Q v * (1 - F v)) =
        (∫ v in 0..ω, Q v) - ∫ v in 0..ω, Q v * F v := by
    calc
      (∫ v in 0..ω, Q v * (1 - F v))
          = ∫ v in 0..ω, Q v - Q v * F v := by
            refine intervalIntegral.integral_congr_ae ?_
            filter_upwards with v hv_mem
            ring
      _ = (∫ v in 0..ω, Q v) - ∫ v in 0..ω, Q v * F v := by
            rw [intervalIntegral.integral_sub hQ hQF]
  exact hsurvival.trans hibp.symm
