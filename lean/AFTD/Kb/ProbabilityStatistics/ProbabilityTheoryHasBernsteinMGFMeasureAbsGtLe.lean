import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.ProbabilityTheoryHasBernsteinMGF
import AFTD.Kb.ProbabilityStatistics.ProbabilityTheoryHasBernsteinMGFMeasureGeLe
import AFTD.Kb.ProbabilityStatistics.ProbabilityTheoryHasBernsteinMGFMeasureLeLe

/-!
# ProbabilityTheory.HasBernsteinMGF.measure_abs_gt_le

Topic: concentration   Node: e27049b5c04e

Provenance: helper lemma. TCSlib, `ProbabilityTheory.HasBernsteinMGF.measure_abs_gt_le`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/Bernstein.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Two-sided Bernstein tail bound. Let $X : \Omega \to \bbr$ be a random variable on a probability space $(\Omega, \mu)$,
and let $c, t_{\max} \ge 0$ be real parameters such that $X$ satisfies the Bernstein
moment generating function condition with parameters $c$ and $t_{\max}$: for every $t$
with $\abs{t} \le t_{\max}$ the exponential moment $e^{tX}$ is $\mu$-integrable and
$\E_\mu[e^{tX}] \le e^{c t^2}$. If $c > 0$, then for every $s$ with $0 \le s \le 2 c\,
t_{\max}$,
\[
\mu\bigl(\{\omega \mid s < \abs{X(\omega)}\}\bigr) \;\le\;
2\exp\!\Bigl(-\frac{s^2}{4c}\Bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real in
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} in
variable {X : Ω → ℝ} {μ : Measure Ω} {c tmax : ℝ} in
/-- **Two-sided Bernstein bound.** If `X` has a Bernstein-type MGF with parameters `(c, tmax)` under a probability measure `μ`, `c > 0`, and `0 ≤ s ≤ 2c·tmax`, then the probability of the event `{s < |X|}` is at most `2·exp(−s²/(4c))`. This is the two-sided form of the Chernoff step in [Ver18, proof of Thm 2.8.1], with the same single-parameter deviation as `measure_ge_le`. **Proof sketch.** Step 1: the event `{s < |X|}` is contained in the union of the two one-sided events `{s ≤ X}` and `{X ≤ −s}`. Step 2: by monotonicity and the union bound its probability is at most the sum of the two one-sided probabilities, each of which is at most `exp(−s²/(4c))` by `measure_ge_le` and `measure_le_le`. -/
lemma ProbabilityTheory.HasBernsteinMGF.measure_abs_gt_le {μ : Measure Ω} [IsProbabilityMeasure μ]
    (h : HasBernsteinMGF X μ c tmax)
    (hc : 0 < c) (s : ℝ) (hs_pos : 0 ≤ s) (hs_le : s ≤ 2 * c * tmax) :
    (μ {ω | s < |X ω|}).toReal ≤ 2 * Real.exp (-s ^ 2 / (4 * c)) := by
  -- Step 1: bad event ⊆ {s ≤ X} ∪ {X ≤ -s}.
  have hsubset : {ω | s < |X ω|} ⊆ {ω | s ≤ X ω} ∪ {ω | X ω ≤ -s} := by
    intro ω hω
    rw [Set.mem_setOf_eq] at hω
    rw [Set.mem_union, Set.mem_setOf_eq, Set.mem_setOf_eq]
    by_contra h_neither
    rw [not_or] at h_neither
    obtain ⟨h1, h2⟩ := h_neither
    have hXlt : X ω < s := lt_of_not_ge h1
    have hXgt : -s < X ω := lt_of_not_ge h2
    have habs_lt : |X ω| < s := abs_lt.mpr ⟨hXgt, hXlt⟩
    exact (lt_irrefl s) (lt_of_lt_of_le hω habs_lt.le)
  -- Step 2: apply union + the two single-tail bounds.
  calc (μ {ω | s < |X ω|}).toReal
      ≤ (μ ({ω | s ≤ X ω} ∪ {ω | X ω ≤ -s})).toReal :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
    _ ≤ (μ {ω | s ≤ X ω}).toReal + (μ {ω | X ω ≤ -s}).toReal := by
        rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
        exact ENNReal.toReal_mono
          (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
          (measure_union_le _ _)
    _ ≤ Real.exp (-s ^ 2 / (4 * c)) + Real.exp (-s ^ 2 / (4 * c)) := by
        gcongr
        · exact h.measure_ge_le hc s hs_pos hs_le
        · exact h.measure_le_le hc s hs_pos hs_le
    _ = 2 * Real.exp (-s ^ 2 / (4 * c)) := by ring
