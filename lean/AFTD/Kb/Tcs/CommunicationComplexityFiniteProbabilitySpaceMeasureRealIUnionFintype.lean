import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.FiniteProbabilitySpace.measureReal_iUnion_fintype

Topic: communication   Node: 7594694b10be

Provenance: helper lemma. TCSlib, `CommunicationComplexity.FiniteProbabilitySpace.measureReal_iUnion_fintype`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/FiniteProbabilitySpace.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finite additivity of the probability measure. Let $\Omega$ be a finite probability space and let $\iota$ be a finite index set. If
$(A_i)_{i \in \iota}$ is a pairwise disjoint family of subsets of $\Omega$, then the
probability of their union is the sum of their probabilities:
\[
\mathbb{P}\!\Bigl(\bigcup_{i \in \iota} A_i\Bigr) \;=\; \sum_{i \in \iota}
\mathbb{P}(A_i),
\]
where $\mathbb{P}(\,\cdot\,) \in \bbr$ denotes the real-valued probability measure of
$\Omega$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ProbabilityTheory in
/-- The real-valued measure of a finite disjoint union is the sum of the real-valued measures of its parts. -/
theorem CommunicationComplexity.FiniteProbabilitySpace.measureReal_iUnion_fintype
    {Ω ι : Type*} [FiniteProbabilitySpace Ω] [Fintype ι]
    (A : ι → Set Ω) (hdisj : Pairwise (fun i j => Disjoint (A i) (A j))) :
    volume.real (⋃ i, A i) = ∑ i, volume.real (A i) := by
  rw [Measure.real]
  rw [measure_iUnion hdisj (fun _ => MeasurableSet.of_discrete),
    tsum_fintype, ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)]
  simp [Measure.real]
