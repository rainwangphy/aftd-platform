import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.BadSingle
import AFTD.Kb.ProbabilityStatistics.BadPair
import AFTD.Kb.ProbabilityStatistics.IsJLEmbedding
import AFTD.Kb.ProbabilityStatistics.JlUnionBound
import AFTD.Kb.ProbabilityStatistics.InstMeasurableSpaceMatrixFinRealTCSlib
import AFTD.Kb.ProbabilityStatistics.JLDistortion

/-!
# exists_isJLEmbedding_of_pair_bound

Topic: concentration   Node: 496b6ce9a0c9

Provenance: helper lemma. TCSlib, `exists_isJLEmbedding_of_pair_bound`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/UnionBound.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Probabilistic method for JL embeddings. Let $\mu$ be a probability measure on $\Omega$, let
$A : \Omega \to \mathbb{R}^{k\times d}$ be a measurable random matrix, let
$\varepsilon\in\mathbb{R}$, and let $V$ be a finite subset of $\mathbb{R}^d$.
Suppose that for every ordered pair $u, v \in V$ the bad event
$\{\omega \mid \texttt{BadSingle}\,\varepsilon\,(A\,\omega)\,(u-v)\}$ is
measurable and has probability at most $2\exp(-k\varepsilon^2/8)$, and that
the union-bound failure probability satisfies
\[
  |V|^2 \cdot 2\exp(-k\varepsilon^2/8) < 1 .
\]
Then there exists a linear map $f : \mathbb{R}^d \to \mathbb{R}^k$ which is an
$\varepsilon$-JL embedding of $V$, i.e.\ $(1-\varepsilon)\|u-v\|^2 \le
\|f u - f v\|^2 \le (1+\varepsilon)\|u-v\|^2$ for all $u, v \in V$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Probabilistic method for JL (shared tail)** [DG03, proof of Thm 2.1]; [Ver18, proof of Thm 5.3.1]. Given a random matrix `A` whose per-pair distortion events `{ω | BadSingle ε (A ω) (u − v)}` are measurable and each have probability at most `2·exp(−kε²/8)`, and such that the union-bound failure probability `|V|² · 2 · exp(−kε²/8)` is strictly less than `1`, some realization `A ω` is an `ε`-JL embedding of `V`. This is the common tail of `johnson_lindenstrauss_of_gaussian` and `johnson_lindenstrauss_of_subgaussian`. **Proof sketch.** Step 1: the union bound `jl_union_bound` bounds the probability of the bad-pair event by `|V|² · 2 · exp(−kε²/8)`. Step 2: by hypothesis this is strictly less than `1`. Step 3: hence some sample `ω` is not bad — otherwise the bad-pair event would be the whole space, of probability `1`. Step 4: the linear map `(A ω).toEuclideanLin` of that witness is an `ε`-JL embedding of `V`, since every pair satisfies the distortion bound. -/
theorem exists_isJLEmbedding_of_pair_bound
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hA_meas : Measurable A)
    (ε : ℝ)
    (V : Finset (EuclideanSpace ℝ (Fin d)))
    (hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
        MeasurableSet {ω | BadSingle ε (A ω) (u - v)})
    (hPair : ∀ u ∈ V, ∀ v ∈ V,
        (μ {ω | BadSingle ε (A ω) (u - v)}).toReal ≤
          2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8))
    (hFail : (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) < 1) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Step 1: Union bound over pairs.
  have hBP : (μ {ω | BadPair ε V (A ω)}).toReal ≤
      (V.card : ℝ) ^ 2 * (2 * Real.exp (-(k : ℝ) * ε ^ 2 / 8)) :=
    jl_union_bound μ A hA_meas V ε hBadMeas hPair
  -- Step 2: Failure probability strictly less than 1.
  have hBadLT1 : (μ {ω | BadPair ε V (A ω)}).toReal < 1 := lt_of_le_of_lt hBP hFail
  -- Step 3: Therefore some ω is *not* bad.
  have hGood : ∃ ω, ¬ BadPair ε V (A ω) := by
    by_contra hNG
    push_neg at hNG
    have hUniv : {ω | BadPair ε V (A ω)} = Set.univ :=
      Set.eq_univ_of_forall hNG
    rw [hUniv, measure_univ] at hBadLT1
    simp at hBadLT1
  -- Step 4: Extract witness, produce embedding.
  obtain ⟨ω, hω⟩ := hGood
  refine ⟨(A ω).toEuclideanLin, ?_⟩
  intro u hu v hv
  by_contra hbd
  exact hω ⟨u, hu, v, hv, hbd⟩
