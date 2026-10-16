import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.BadSingle
import AFTD.Kb.ProbabilityStatistics.BadPair
import AFTD.Kb.ProbabilityStatistics.JLDistortionOfNotBad
import AFTD.Kb.ProbabilityStatistics.InstMeasurableSpaceMatrixFinRealTCSlib
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.ProbabilityStatistics.JLDistortion
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# jl_union_bound

Topic: concentration   Node: e84c35973869

Provenance: helper lemma. TCSlib, `jl_union_bound`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Union bound for Johnson–Lindenstrauss distortion. Let $(\Omega,\mu)$ be a probability space, and let $A\colon\Omega\to\bbr^{k\times d}$ be
a measurable random $k\times d$ matrix. Fix a finite set $V\subseteq\bbr^d$ and a
parameter $\varepsilon\in\bbr$, and suppose that for every pair $u,v\in V$ the
single-vector bad event for the difference $u-v$ has probability at most
$2\exp(-k\varepsilon^2/8)$, that is,
\[
\mu\bigl\{\,\omega : \varepsilon\,\|u-v\|^2 < \bigl|\,\|A(\omega)(u-v)\|^2 -
\|u-v\|^2\,\bigr|\,\bigr\} \le 2\exp\!\bigl(-k\varepsilon^2/8\bigr).
\]
Then the probability of the bad-pair event — that some ordered pair $(u,v)\in V\times V$
fails the two-sided distortion bound $(1-\varepsilon)\|u-v\|^2 \le \|A(\omega)(u-v)\|^2
\le (1+\varepsilon)\|u-v\|^2$ — is at most
\[
  |V|^2 \cdot 2\exp\!\bigl(-k\varepsilon^2/8\bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **JL union bound** [DG03, proof of Thm 2.1]. Given that each pair's distortion event has probability `≤ 2·exp(−kε²/8)`, the probability that *some* ordered pair in `V × V` is distorted is at most `|V|² · 2 · exp(−kε²/8)`. Deviation: the union is over all `|V|²` ordered pairs (including `u = v`) rather than the source's `C(n, 2)` unordered pairs; this only loosens the constant. **Proof sketch.** Step 1: the bad-pair event is contained in the double union over `u, v ∈ V` of the per-pair bad events `{ω | BadSingle ε (A ω) (u − v)}`, by `JLDistortion.of_not_bad`. Step 2: monotonicity and finite subadditivity of the measure (`measure_biUnion_finset_le`, applied twice) bound the measure of the bad-pair event by the double sum of the per-pair measures. Step 3: all these measures are finite, so the double sum passes to real numbers. Step 4: bound each of the `|V|²` real summands by `2·exp(−kε²/8)` and collect. -/
theorem jl_union_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (_hA_meas : Measurable A)
    (V : Finset (EuclideanSpace ℝ (Fin d)))
    (ε : ℝ)
    (_hBadMeasurable : ∀ u ∈ V, ∀ v ∈ V,
      MeasurableSet {ω | BadSingle ε (A ω) (u - v)})
    (hpair : ∀ u ∈ V, ∀ v ∈ V,
      (μ {ω | BadSingle ε (A ω) (u - v)}).toReal ≤
        2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) :
    (μ {ω | BadPair ε V (A ω)}).toReal ≤
        (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
  -- Step 1: the bad-pair event is contained in the union of per-pair bad-single events.
  have hsub : {ω | BadPair ε V (A ω)} ⊆
      ⋃ u ∈ V, ⋃ v ∈ V, {ω | BadSingle ε (A ω) (u - v)} := by
    intro ω hω
    obtain ⟨u, hu, v, hv, hbad⟩ := hω
    refine Set.mem_iUnion₂.mpr ⟨u, hu, Set.mem_iUnion₂.mpr ⟨v, hv, ?_⟩⟩
    by_contra hnot
    exact hbad (JLDistortion.of_not_bad ε u v (A ω) hnot)
  -- Step 2: measure subadditivity over the finite double union.
  have hmeas_le : μ {ω | BadPair ε V (A ω)} ≤
      ∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)} := by
    calc μ {ω | BadPair ε V (A ω)}
        ≤ μ (⋃ u ∈ V, ⋃ v ∈ V, {ω | BadSingle ε (A ω) (u - v)}) :=
          measure_mono hsub
      _ ≤ ∑ u ∈ V, μ (⋃ v ∈ V, {ω | BadSingle ε (A ω) (u - v)}) :=
          measure_biUnion_finset_le V _
      _ ≤ ∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)} := by
          gcongr with u _
          exact measure_biUnion_finset_le V _
  -- Step 3: all per-pair measures are finite (μ is a probability measure), so the
  -- double sum passes to `ℝ`.
  have hne_top : ∀ u ∈ V, ∀ v ∈ V,
      μ {ω | BadSingle ε (A ω) (u - v)} ≠ ⊤ :=
    fun u _ v _ => measure_ne_top _ _
  have hBP_ne_top : μ {ω | BadPair ε V (A ω)} ≠ ⊤ := measure_ne_top _ _
  have hInnerSum_ne_top : ∀ u ∈ V,
      (∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)}) ≠ ⊤ := fun u hu => by
    rw [← lt_top_iff_ne_top, ENNReal.sum_lt_top]
    exact fun v hv => (hne_top u hu v hv).lt_top
  have hSum_ne_top :
      (∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)}) ≠ ⊤ := by
    rw [← lt_top_iff_ne_top, ENNReal.sum_lt_top]
    exact fun u hu => (hInnerSum_ne_top u hu).lt_top
  have hsum_toReal :
      (∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)}).toReal =
        ∑ u ∈ V, ∑ v ∈ V, (μ {ω | BadSingle ε (A ω) (u - v)}).toReal := by
    rw [ENNReal.toReal_sum (fun u hu => hInnerSum_ne_top u hu)]
    exact Finset.sum_congr rfl
      (fun u hu => ENNReal.toReal_sum (fun v hv => hne_top u hu v hv))
  calc (μ {ω | BadPair ε V (A ω)}).toReal
      ≤ (∑ u ∈ V, ∑ v ∈ V, μ {ω | BadSingle ε (A ω) (u - v)}).toReal :=
        (ENNReal.toReal_le_toReal hBP_ne_top hSum_ne_top).mpr hmeas_le
    _ = ∑ u ∈ V, ∑ v ∈ V, (μ {ω | BadSingle ε (A ω) (u - v)}).toReal :=
        hsum_toReal
    -- Step 4: bound each of the `|V|²` summands and collect.
    _ ≤ ∑ u ∈ V, ∑ v ∈ V, 2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := by
        gcongr with u hu v hv
        exact hpair u hu v hv
    _ = (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) := by
        simp [Finset.sum_const, sq]
        ring
