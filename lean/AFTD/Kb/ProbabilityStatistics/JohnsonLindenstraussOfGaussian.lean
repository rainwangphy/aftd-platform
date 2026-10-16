import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.BadSingle
import AFTD.Kb.ProbabilityStatistics.IsJLEmbedding
import AFTD.Kb.ProbabilityStatistics.ExistsIsJLEmbeddingOfPairBound
import AFTD.Kb.ProbabilityStatistics.JlConcentrationSingle
import AFTD.Kb.ProbabilityStatistics.InstMeasurableSpaceMatrixFinRealTCSlib

/-!
# johnson_lindenstrauss_of_gaussian

Topic: concentration   Node: 5626bafed9b8

Provenance: helper lemma. TCSlib, `johnson_lindenstrauss_of_gaussian`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Johnson–Lindenstrauss embedding from a Gaussian matrix. Fix dimensions $d$ and $k$ with $k \ge 1$, a distortion parameter $\varepsilon \in
(0,1)$, and a finite set of points $V \subseteq \bbr^d$. Let $A$ be a random $k \times
d$ matrix whose entries $A_{ij}$ are independent Gaussian random variables, each with
mean $0$ and variance $1/k$. If the union-bound quantity satisfies
\[
  |V|^2 \cdot 2\exp\!\left(-\,k\varepsilon^2/8\right) < 1,
\]
then there exists a linear map $f : \bbr^d \to \bbr^k$ that is an $\varepsilon$-JL
embedding of $V$: for every pair $u, v \in V$,
\[
  (1-\varepsilon)\,\|u-v\|^2 \;\le\; \|f(u)-f(v)\|^2 \;\le\; (1+\varepsilon)\,\|u-v\|^2.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Structural JL via the probabilistic method (Gaussian)** [DG03, proof of Thm 2.1]; [Ver18, proof of Thm 5.3.1]. Given a random matrix with iid `N(0, 1/k)` entries on a probability space (rows independent, entries independent within each row) AND that the union-bound failure probability `|V|² · 2 · exp(-kε²/8)` is strictly less than `1`, there exists a realization of the random matrix that is an `ε`-JL embedding of `V`. **Proof sketch.** Step 1: the single-vector concentration bound `jl_concentration_single`, applied to each difference `u − v` with `u, v ∈ V`, gives the per-pair bound `2·exp(−kε²/8)`. Step 2: the shared probabilistic-method lemma `exists_isJLEmbedding_of_pair_bound` (union bound, failure probability `< 1`, extraction of a good sample) produces the embedding. -/
theorem johnson_lindenstrauss_of_gaussian (hk_pos : 0 < k)
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hA_meas : Measurable A)
    (hA_law : ∀ (i : Fin k) (j : Fin d),
      Measure.map (fun ω => A ω i j) μ =
        gaussianReal 0 ⟨1 / k, by positivity⟩)
    (hRowEntryIndep : ∀ i : Fin k, iIndepFun (fun (j : Fin d) ω => A ω i j) μ)
    (hRowsIndep : iIndepFun (fun (i : Fin k) (ω : Ω) (j : Fin d) => A ω i j) μ)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (V : Finset (EuclideanSpace ℝ (Fin d)))
    (hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
        MeasurableSet {ω | BadSingle ε (A ω) (u - v)})
    (hFail : (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Step 1: Concentration per pair (Gaussian single-vector bound).
  have hPair : ∀ u ∈ V, ∀ v ∈ V,
      (μ {ω | BadSingle ε (A ω) (u - v)}).toReal ≤
        2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8) := fun u _ v _ =>
    jl_concentration_single hk_pos μ A hA_meas hA_law hRowEntryIndep hRowsIndep
      (u - v) ε hε_pos hε_lt
  -- Step 2: Union bound and probabilistic method.
  exact exists_isJLEmbedding_of_pair_bound μ A hA_meas ε V hBadMeas hPair hFail
