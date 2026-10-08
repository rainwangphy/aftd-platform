import AFTD.Prelude

/-!
# CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.prob_many_events_le

Topic: communication   Node: 027097efe445

Provenance: helper lemma. TCSlib, `CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.prob_many_events_le`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Derandomization.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Hoeffding tail bound for a sum of bounded independent variables. Let $(\Omega', \mu)$ be a probability space, let $t \ge 1$, and let $Y_0, \dots, Y_{t-1}
: \Omega' \to \bbr$ be mutually independent, almost everywhere measurable random
variables that almost surely take values in $[0,1]$. Suppose $\E[Y_i] \le \varepsilon$
for every $i$, where $0 \le \varepsilon$, and let $c > 1$. Then
\[
\mu\!\left\{\omega \;\middle|\; c\,\varepsilon\,t \le \sum_{i=0}^{t-1}
Y_i(\omega)\right\}
  \;\le\;
  \exp\!\left(-2(c-1)^2\varepsilon^2 t\right).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory in
/-- Hoeffding-type tail bound: if `Y₀, …, Y_{t−1}` are independent `[0,1]`-valued random variables each with mean at most `ε ≥ 0`, then for every `c > 1` the probability that their sum is at least `c · ε · t` is at most `exp(−2 (c−1)² ε² t)`. **Proof sketch.** Centre the variables, `Xᵢ = Yᵢ − E[Yᵢ]`; the centred family is still independent, and each `Xᵢ` is sub-Gaussian with parameter `(1/2)²` because `Yᵢ` takes values in an interval of length one. Mathlib's Hoeffding bound for sums of independent sub-Gaussian variables gives the tail of `∑ Xᵢ` at threshold `(c−1) ε t`. Since `∑ E[Yᵢ] ≤ ε t`, the event `{∑ Yᵢ ≥ c ε t}` is contained in `{∑ Xᵢ ≥ (c−1) ε t}`; conclude by monotonicity of the measure and simplification of the exponent. -/
theorem CommunicationComplexity.PublicCoin.FiniteMessage.Protocol.prob_many_events_le
    {Ω' : Type*} [MeasurableSpace Ω'] {μ : Measure Ω'} [IsProbabilityMeasure μ]
    {t : ℕ} {Y : Fin t → Ω' → ℝ} {ε : ℝ} {c : ℝ}
    (hindep : iIndepFun Y μ)
    (hmeas : ∀ i, AEMeasurable (Y i) μ)
    (h01 : ∀ i, ∀ᵐ ω ∂μ, Y i ω ∈ Set.Icc (0 : ℝ) 1)
    (hmean : ∀ i, ∫ ω, Y i ω ∂μ ≤ ε)
    (hε : 0 ≤ ε) (hc : 1 < c)
    (ht : 0 < t) :
    μ.real {ω | c * ε * t ≤ ∑ i, Y i ω}
      ≤ Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * t) := by
  -- Center the variables: X i ω = Y i ω - E[Y i]
  set X : Fin t → Ω' → ℝ := fun i ω => Y i ω - ∫ x, Y i x ∂μ
  -- Independence of centered family
  have hindepX : iIndepFun X μ :=
    hindep.comp (fun i (y : ℝ) => y - ∫ x, Y i x ∂μ)
      (fun i => measurable_id.sub measurable_const)
  -- Sub-Gaussianity with parameter (1/2)^2
  have hsubG : ∀ i : Fin t,
      HasSubgaussianMGF (X i) (((1 : NNReal) / 2) ^ 2) μ :=
    fun i => by convert hasSubgaussianMGF_of_mem_Icc (a := (0 : ℝ)) (b := 1) (hmeas i) (h01 i)
              using 2; simp
  -- Hoeffding tail bound for ∑ X_i with threshold (c-1)*ε*t
  have htail := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
    (ι := Fin t) hindepX (s := Finset.univ)
    (c := fun _ => ((1 : NNReal) / 2) ^ 2)
    (fun i _ => hsubG i) (ε := (c - 1) * ε * ↑t)
    (by apply mul_nonneg
        · apply mul_nonneg <;> linarith
        · exact Nat.cast_nonneg _)
  -- Mean bound: ∑ E[Y_i] ≤ εt
  have hmean_sum : ∑ i : Fin t, ∫ x, Y i x ∂μ ≤ ε * ↑t := by
    calc ∑ i : Fin t, ∫ x, Y i x ∂μ
        ≤ ∑ _ : Fin t, ε := Finset.sum_le_sum (fun i _ => hmean i)
      _ = ε * ↑t := by simp [Finset.sum_const, mul_comm]
  -- Set inclusion: {∑ Y ≥ c*ε*t} ⊆ {∑ X ≥ (c-1)*ε*t}
  have hsubset : {ω | c * ε * ↑t ≤ ∑ i, Y i ω} ⊆
      {ω | (c - 1) * ε * ↑t ≤ ∑ i ∈ Finset.univ, X i ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hsub : ∑ i : Fin t, X i ω =
        ∑ i, Y i ω - ∑ i, ∫ x, Y i x ∂μ := by
      simp only [X, Finset.sum_sub_distrib]
    nlinarith [hsub, hmean_sum]
  -- Monotonicity + exponent simplification
  calc μ.real {ω | c * ε * ↑t ≤ ∑ i, Y i ω}
      ≤ μ.real {ω | (c - 1) * ε * ↑t ≤ ∑ i ∈ Finset.univ, X i ω} :=
        measureReal_mono hsubset
    _ ≤ _ := htail
    _ = Real.exp (-2 * (c - 1) ^ 2 * ε ^ 2 * ↑t) := by
        congr 1
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        push_cast
        have ht_pos : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
        field_simp
        ring
