import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.JlFailureBoundOfDim
import AFTD.Kb.ProbabilityStatistics.ExistsIidGaussianMatrix
import AFTD.Kb.ProbabilityStatistics.MeasurableSetBadSingle
import AFTD.Kb.ProbabilityStatistics.BadSingle
import AFTD.Kb.ProbabilityStatistics.IsJLEmbedding
import AFTD.Kb.ProbabilityStatistics.JohnsonLindenstraussOfGaussian
import AFTD.Kb.ProbabilityStatistics.InstMeasurableSpaceMatrixFinRealTCSlib

/-!
# johnson_lindenstrauss

Topic: concentration   Node: a8366b8eb270

Provenance: formalization of a published result. Source: Johnson–Lindenstrauss flattening lemma, as formalized in TCSlib (`johnson_lindenstrauss`). Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Johnson–Lindenstrauss flattening lemma. Let $0 < \varepsilon < 1$ and let $n \ge 2$ be an integer. Suppose the target dimension
$k$ satisfies $k \ge 32\,\log n / \varepsilon^2$. Then for every finite set $V \subseteq
\bbr^d$ of at most $n$ points there exists a linear map $f : \bbr^d \to \bbr^k$ that is
an $\varepsilon$-JL embedding of $V$; that is,
\[
(1 - \varepsilon)\,\norm{u - v}^2 \;\le\; \norm{f(u) - f(v)}^2 \;\le\; (1 +
\varepsilon)\,\norm{u - v}^2
\]
for all $u, v \in V$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Johnson–Lindenstrauss flattening lemma (standard form)** [DG03, Thm 2.1]; [Ver18, Thm 5.3.1]; origin [JL84, Lemma 1]. For any `0 < ε < 1`, any `n ≥ 2`, and target dimension `k` with `k ≥ 32 · log n / ε²`, every finite set `V` of at most `n` points in `ℝ^d` admits a linear embedding `f : ℝ^d → ℝ^k` preserving pairwise squared distances up to factor `(1 ± ε)`. The embedding is a realization of a matrix with iid `N(0, 1/k)` entries; the proof is axiom-free. Deviation: the dimension bound is `k ≥ 32 · log n / ε²`, whereas [DG03] obtains `k ≥ 4 (ε²/2 − ε³/3)⁻¹ log n` and [Ver18] states `k ≥ C ε⁻² log n` for an unspecified constant; the conclusion is stated for squared distances (see `johnson_lindenstrauss_dist` for the distance form). The `32` is not tight: it is chosen for cleanness of the numerical bookkeeping, giving `|V|² · 2 · exp(-kε²/8) ≤ 1/2`. **Proof sketch.** Step 1: numerical bookkeeping (`jl_failure_bound_of_dim`): the dimension hypothesis gives `k > 0` and the union-bound failure probability `|V|² · 2 · exp(−kε²/8)` is strictly less than `1`. Step 2: realize an iid `N(0, 1/k)` matrix `A` on a probability space (`exists_iid_gaussian_matrix`) and check that its per-pair bad events are measurable (`measurableSet_badSingle`). Step 3: the structural theorem `johnson_lindenstrauss_of_gaussian` (single-vector concentration, union bound, probabilistic method) extracts a good realization. -/
theorem johnson_lindenstrauss
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1)
    (n : ℕ) (hn : 2 ≤ n)
    (hk : (32 : ℝ) * Real.log n / ε ^ 2 ≤ k)
    (V : Finset (EuclideanSpace ℝ (Fin d))) (hV : V.card ≤ n) :
    ∃ f : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] EuclideanSpace ℝ (Fin k),
      IsJLEmbedding ε V f := by
  -- Step 1: numerical bookkeeping: k > 0 and union-bound failure prob < 1.
  obtain ⟨hk_pos, hFail⟩ :=
    jl_failure_bound_of_dim ε hε_pos n hn hk V hV
  -- Step 2: obtain a Gaussian probability space; the per-pair bad events are measurable.
  obtain ⟨Ω, _, μ, _, A, hA_meas, hA_law, hRowEntryIndep, hRowsIndep⟩ :=
    exists_iid_gaussian_matrix hk_pos d
  have hBadMeas : ∀ u ∈ V, ∀ v ∈ V,
      MeasurableSet {ω | BadSingle ε (A ω) (u - v)} :=
    fun u _ v _ => measurableSet_badSingle A hA_meas (u - v) ε
  -- Step 3: invoke the structural theorem `_of_gaussian`.
  exact johnson_lindenstrauss_of_gaussian hk_pos μ A hA_meas hA_law
    hRowEntryIndep hRowsIndep ε hε_pos hε_lt V hBadMeas hFail
