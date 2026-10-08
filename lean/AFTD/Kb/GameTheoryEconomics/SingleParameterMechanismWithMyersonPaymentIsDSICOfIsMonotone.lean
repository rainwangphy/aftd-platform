import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPayment
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismWithMyersonPayment
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismWithMyersonPaymentQuasiLinearUtilityEq
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.Tcs.G

/-!
# SingleParameterMechanism.withMyersonPayment_isDSIC_of_isMonotone

Topic: mechanism_design   Node: 10a37a6d983c

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.withMyersonPayment_isDSIC_of_isMonotone`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Myerson Lemma, Property 2: a monotone allocation rule is DSIC when paired with the canonical Myerson payment rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- Myerson Lemma, Property 2: a monotone allocation rule is DSIC when paired with the canonical Myerson payment rule. -/
theorem SingleParameterMechanism.withMyersonPayment_isDSIC_of_isMonotone [DecidableEq I]
    {x : (I → ℝ) → I → ℝ}
    (hx : IsMonotone ({ allocationRule := x, paymentRule := myersonPayment x } :
      SingleParameterMechanism I ℝ)) :
    (withMyersonPayment x).IsDSIC := by
  intro v i (s' : ℝ) (reports : I → ℝ)
  let g : ℝ → ℝ := fun z => x (Function.update reports i z) i
  have hgmono : Monotone g := by
    intro z₁ z₂ hz
    exact hx i z₁ z₂ hz reports
  have hform : ∀ r : ℝ,
      (withMyersonPayment x).quasiLinearUtility (Function.update reports i r) v i =
        (v i - r) * g r + ∫ z in 0..r, g z := by
    intro r
    rw [withMyersonPayment_quasiLinearUtility_eq]
    simp [g, Function.update_idem]
  change
    (withMyersonPayment x).quasiLinearUtility (Function.update reports i s') v i ≤
      (withMyersonPayment x).quasiLinearUtility (Function.update reports i (v i)) v i
  by_cases hs : s' ≤ v i
  · have hg0s : IntervalIntegrable g MeasureTheory.volume 0 s' := hgmono.intervalIntegrable
    have hgsv : IntervalIntegrable g MeasureTheory.volume s' (v i) := hgmono.intervalIntegrable
    have hmonoInt :
        (v i - s') * g s' ≤ ∫ z in s'..v i, g z := by
      simpa using
        intervalIntegral.integral_mono_on hs intervalIntegrable_const hgsv
          (fun z hz => hgmono hz.1)
    calc
      (withMyersonPayment x).quasiLinearUtility (Function.update reports i s') v i
          = (v i - s') * g s' + ∫ z in 0..s', g z := hform s'
      _ ≤ (∫ z in s'..v i, g z) + ∫ z in 0..s', g z := by
        exact add_le_add hmonoInt le_rfl
      _ = ∫ z in 0..v i, g z := by
        simpa [add_comm] using intervalIntegral.integral_add_adjacent_intervals hg0s hgsv
      _ = (withMyersonPayment x).quasiLinearUtility (Function.update reports i (v i)) v i := by
        rw [hform (v i)]
        ring
  · have hvs : v i ≤ s' := le_of_not_ge hs
    have hg0v : IntervalIntegrable g MeasureTheory.volume 0 (v i) := hgmono.intervalIntegrable
    have hgvs : IntervalIntegrable g MeasureTheory.volume (v i) s' := hgmono.intervalIntegrable
    have hbracket : (v i - s') * g s' + ∫ z in v i..s', g z ≤ 0 := by
      have hmonoInt : ∫ z in v i..s', g z ≤ (s' - v i) * g s' := by
        simpa using
          intervalIntegral.integral_mono_on hvs hgvs intervalIntegrable_const
            (fun z hz => hgmono hz.2)
      nlinarith
    calc
      (withMyersonPayment x).quasiLinearUtility (Function.update reports i s') v i
          = (v i - s') * g s' + ∫ z in 0..s', g z := hform s'
      _ = (v i - s') * g s' + ((∫ z in 0..v i, g z) + ∫ z in v i..s', g z) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals hg0v hgvs]
      _ = (∫ z in 0..v i, g z) + ((v i - s') * g s' + ∫ z in v i..s', g z) := by
        ring
      _ ≤ ∫ z in 0..v i, g z + 0 := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right hbracket (∫ z in 0..v i, g z)
      _ = ∫ z in 0..v i, g z := by simp
      _ = (withMyersonPayment x).quasiLinearUtility (Function.update reports i (v i)) v i := by
        rw [hform (v i)]
        ring
