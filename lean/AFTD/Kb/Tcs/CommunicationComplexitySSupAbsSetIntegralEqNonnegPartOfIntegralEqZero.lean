import AFTD.Prelude

/-!
# CommunicationComplexity.sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero

Topic: information   Node: e862a6d71f29

Provenance: helper lemma. TCSlib, `CommunicationComplexity.sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Supremum of absolute set-integrals of a mean-zero function. Let $\mu$ be a finite measure on a measurable space $\Omega$, and let $g \colon \Omega
\to \bbr$ be measurable and integrable with mean zero, $\int_\Omega g\,d\mu = 0$. Then
the supremum of $\abs{\int_S g\,d\mu}$ taken over all measurable sets $S \subseteq
\Omega$ equals the integral of $g$ over the region where it is nonnegative:
\[
\sup_{S\text{ measurable}} \abs*{\int_S g\,d\mu} \;=\; \int_{\{x \,:\, g(x) \ge 0\}}
g\,d\mu.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- For an integrable function `g` with mean zero, the supremum over measurable sets `S` of `|∫_S g|` is attained at `S = {g ≥ 0}` and equals `∫_{g ≥ 0} g`. **Proof sketch.** Write `pos = ∫_{g ≥ 0} g ≥ 0`. Step 1: for every measurable `S`, both `∫_S g ≤ pos` and `∫_{Sᶜ} g ≤ pos` (dropping the negative part of `g` only increases a set integral), and `∫_{Sᶜ} g = −∫_S g` by mean zero; so `|∫_S g| ≤ pos`. Step 2: hence the supremum is at most `pos`. Step 3: the set `{g ≥ 0}` itself achieves the value `pos`, so the supremum is at least `pos`. -/
theorem CommunicationComplexity.sSup_abs_setIntegral_eq_nonneg_part_of_integral_eq_zero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {g : Ω → ℝ} (hg_meas : Measurable g) (hg : Integrable g μ)
    (h_mean : ∫ x, g x ∂μ = 0) :
    sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
      |∫ x in (S : Set Ω), g x ∂μ|) =
      ∫ x in {x | 0 ≤ g x}, g x ∂μ := by
  let A : Set Ω := {x | 0 ≤ g x}
  let pos : ℝ := ∫ x in A, g x ∂μ
  have hA : MeasurableSet A := measurableSet_Ici.preimage hg_meas
  have hpos_nonneg : 0 ≤ pos := by
    dsimp [pos, A]
    exact setIntegral_nonneg hA fun x hx => hx
  -- Step 1: every set integral is bounded in absolute value by the positive part
  have hset_le (S : {S : Set Ω // MeasurableSet S}) :
      |∫ x in (S : Set Ω), g x ∂μ| ≤ pos := by
    have hupper : ∫ x in (S : Set Ω), g x ∂μ ≤ pos := by
      simpa [pos, A] using
        setIntegral_le_nonneg (S.property) hg_meas.stronglyMeasurable hg
    have hcompl_upper : ∫ x in ((S : Set Ω)ᶜ), g x ∂μ ≤ pos := by
      simpa [pos, A] using
        setIntegral_le_nonneg (S.property.compl) hg_meas.stronglyMeasurable hg
    have hcompl_eq_neg :
        ∫ x in ((S : Set Ω)ᶜ), g x ∂μ = -∫ x in (S : Set Ω), g x ∂μ := by
      have hdecomp := integral_add_compl S.property hg
      rw [h_mean] at hdecomp
      linarith
    rw [abs_le]
    constructor
    · linarith
    · exact hupper
  -- Step 2: the supremum is at most the positive part
  have hupper_sSup :
      sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), g x ∂μ|) ≤ pos := by
    exact Real.sSup_le (by rintro _ ⟨S, rfl⟩; exact hset_le S) hpos_nonneg
  have hbdd :
      BddAbove (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), g x ∂μ|) :=
    ⟨pos, by rintro _ ⟨S, rfl⟩; exact hset_le S⟩
  -- Step 3: the set `{g ≥ 0}` attains the positive part
  have hlower_sSup :
      pos ≤ sSup (Set.range fun S : {S : Set Ω // MeasurableSet S} =>
        |∫ x in (S : Set Ω), g x ∂μ|) := by
    let Aset : {S : Set Ω // MeasurableSet S} := ⟨A, hA⟩
    have hA_value :
        |∫ x in (Aset : Set Ω), g x ∂μ| = pos := by
      dsimp [Aset, pos]
      rw [abs_of_nonneg hpos_nonneg]
    rw [← hA_value]
    exact le_csSup hbdd (Set.mem_range_self Aset)
  exact le_antisymm hupper_sSup hlower_sSup
