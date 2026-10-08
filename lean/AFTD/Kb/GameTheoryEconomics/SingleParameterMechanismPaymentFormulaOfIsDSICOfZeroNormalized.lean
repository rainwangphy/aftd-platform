import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismWithMyersonPaymentIsDSICOfIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismPaymentDifferenceBound
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotoneOfIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismZeroNormalized
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPayment
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPaymentZeroNormalized
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismWithMyersonPaymentQuasiLinearUtilityEq

/-!
# SingleParameterMechanism.payment_formula_of_isDSIC_of_zeroNormalized

Topic: mechanism_design   Node: 700d1829f46a

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.payment_formula_of_isDSIC_of_zeroNormalized`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Explicit payment identity used in Myerson's Lemma: for a DSIC single-parameter mechanism with zero-normalized payments, the payment rule is given pointwise by the Myerson payment identity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- Explicit payment identity used in Myerson's Lemma: for a DSIC single-parameter mechanism with zero-normalized payments, the payment rule is given pointwise by the Myerson payment identity. -/
theorem SingleParameterMechanism.payment_formula_of_isDSIC_of_zeroNormalized [DecidableEq I]
    {x p : (I → ℝ) → I → ℝ}
    (hdsic : ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (h0 : ZeroNormalized p)
    (b : I → ℝ) (i : I) :
    p b i = b i * x b i - ∫ z in 0..b i, x (Function.update b i z) i := by
  have hx :
      IsMonotone ({ allocationRule := x, paymentRule := p } :
        SingleParameterMechanism I ℝ) :=
    isMonotone_of_isDSIC hdsic
  have hmyersonDSIC :
      ({ allocationRule := x, paymentRule := myersonPayment x } :
        SingleParameterMechanism I ℝ).IsDSIC := by
    exact withMyersonPayment_isDSIC_of_isMonotone (x := x) hx
  have hcompare :
      ∀ y z : ℝ, z ≤ y →
        |(p (Function.update b i y) i - myersonPayment x (Function.update b i y) i) -
            (p (Function.update b i z) i - myersonPayment x (Function.update b i z) i)| ≤
          (y - z) * (x (Function.update b i y) i - x (Function.update b i z) i) := by
    intro y z hyz
    simpa using
      payment_difference_bound (x := x) (p := p) (q := myersonPayment x)
        hdsic hmyersonDSIC b i y z
  have hzero_compare :
      p (Function.update b i 0) i - myersonPayment x (Function.update b i 0) i = 0 := by
    rw [h0]
    exact myersonPayment_zeroNormalized x i b |> Eq.symm |> sub_eq_zero.mpr
  let g : ℝ → ℝ := fun t => x (Function.update b i t) i
  let d : ℝ → ℝ := fun t =>
    p (Function.update b i t) i - myersonPayment x (Function.update b i t) i
  have hgmono : Monotone g := by
    intro s t hst
    exact hx i s t hst b
  have hcompare' :
      ∀ y z : ℝ, z ≤ y → |d y - d z| ≤ (y - z) * (g y - g z) := by
    intro y z hyz
    simpa [d, g] using hcompare y z hyz
  have hd0 : d 0 = 0 := by
    simpa [d] using hzero_compare
  have hpartition :
      ∀ a c : ℝ, a ≤ c → ∀ N : ℕ, 0 < N →
        |d c - d a| ≤ ((c - a) * (g c - g a)) / N := by
    intro a c hac N hN
    let h : ℝ := (c - a) / N
    let t : ℕ → ℝ := fun k => a + k * h
    have hN0 : (N : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hN)
    have hh_nonneg : 0 ≤ h := by
      dsimp [h]
      exact div_nonneg (sub_nonneg.mpr hac) (by positivity)
    have ht0 : t 0 = a := by
      simp [t]
    have htN : t N = c := by
      dsimp [t, h]
      field_simp [hN0]
      ring
    have htstep : ∀ k : ℕ, t (k + 1) - t k = h := by
      intro k
      simp [t, Nat.cast_add, Nat.cast_one]
      ring
    have hstep_bound :
        ∀ k ∈ Finset.range N,
          |d (t (k + 1)) - d (t k)| ≤ h * (g (t (k + 1)) - g (t k)) := by
      intro k hk
      have hkcast : (k : ℝ) ≤ (k + 1 : ℕ) := by
        exact_mod_cast (Nat.le_succ k)
      have hkord : t k ≤ t (k + 1) := by
        dsimp [t]
        simpa [add_comm, add_left_comm, add_assoc] using
          add_le_add_right (mul_le_mul_of_nonneg_right hkcast hh_nonneg) a
      simpa [htstep k] using hcompare' (t (k + 1)) (t k) hkord
    calc
      |d c - d a| = |d (t N) - d (t 0)| := by rw [htN, ht0]
      _ = |Finset.sum (Finset.range N) (fun k => d (t (k + 1)) - d (t k))| := by
        rw [← Finset.sum_range_sub fun k => d (t k)]
      _ ≤ Finset.sum (Finset.range N) (fun k => |d (t (k + 1)) - d (t k)|) := by
        simpa using Finset.abs_sum_le_sum_abs
          (fun k => d (t (k + 1)) - d (t k)) (Finset.range N)
      _ ≤ Finset.sum (Finset.range N) (fun k => h * (g (t (k + 1)) - g (t k))) := by
        exact Finset.sum_le_sum hstep_bound
      _ = h * Finset.sum (Finset.range N) (fun k => g (t (k + 1)) - g (t k)) := by
        rw [← Finset.mul_sum]
      _ = h * (g (t N) - g (t 0)) := by
        rw [Finset.sum_range_sub fun k => g (t k)]
      _ = ((c - a) / N) * (g c - g a) := by simp [h, htN, ht0]
      _ = ((c - a) * (g c - g a)) / N := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
  have hzero_of_abs_le_div_nat :
      ∀ {u A : ℝ}, 0 ≤ A → (∀ N : ℕ, 0 < N → |u| ≤ A / N) → u = 0 := by
    intro u A _ hbound
    have hlim0 : Filter.Tendsto (fun N : ℕ => A / N) Filter.atTop (nhds 0) := by
      simpa [div_eq_mul_inv, one_div] using
        (tendsto_const_nhds.mul tendsto_one_div_atTop_nhds_zero_nat :
          Filter.Tendsto (fun N : ℕ => A * (1 / (N : ℝ))) Filter.atTop (nhds (A * 0)))
    have hlim :
        Filter.Tendsto (fun N : ℕ => A / ((N + 1 : ℕ) : ℝ)) Filter.atTop (nhds 0) := by
      simpa [Function.comp_def] using hlim0.comp (Filter.tendsto_add_atTop_nat 1)
    have hzero : Filter.Tendsto (fun _ : ℕ => |u|) Filter.atTop (nhds 0) :=
      squeeze_zero (fun _ => abs_nonneg u) (fun N => hbound (N + 1) (Nat.succ_pos N)) hlim
    exact abs_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hzero)
  have hdb0 : d (b i) - d 0 = 0 := by
    by_cases hbi : 0 ≤ b i
    · let A : ℝ := (b i - 0) * (g (b i) - g 0)
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        exact mul_nonneg (sub_nonneg.mpr hbi) (sub_nonneg.mpr (hgmono hbi))
      have hA_bound : ∀ N : ℕ, 0 < N → |d (b i) - d 0| ≤ A / N := by
        intro N hN
        simpa [A, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          hpartition 0 (b i) hbi N hN
      exact hzero_of_abs_le_div_nat hA_nonneg hA_bound
    · have hbi' : b i ≤ 0 := le_of_not_ge hbi
      let A : ℝ := (0 - b i) * (g 0 - g (b i))
      have hA_nonneg : 0 ≤ A := by
        dsimp [A]
        exact mul_nonneg (sub_nonneg.mpr hbi') (sub_nonneg.mpr (hgmono hbi'))
      have hA_bound : ∀ N : ℕ, 0 < N → |d (b i) - d 0| ≤ A / N := by
        intro N hN
        simpa [A, abs_sub_comm, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          hpartition (b i) 0 hbi' N hN
      exact hzero_of_abs_le_div_nat hA_nonneg hA_bound
  have hdb : d (b i) = 0 := by
    rw [hd0, sub_zero] at hdb0
    exact hdb0
  have hp_eq : p b i - myersonPayment x b i = 0 := by
    simpa [d, Function.update_eq_self] using hdb
  simpa [myersonPayment] using sub_eq_zero.mp hp_eq
