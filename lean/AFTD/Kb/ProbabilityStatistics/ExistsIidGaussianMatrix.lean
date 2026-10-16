import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.InstMeasurableSpaceMatrixFinRealTCSlib

/-!
# exists_iid_gaussian_matrix

Topic: concentration   Node: cd2a8e6fa2ad

Provenance: helper lemma. TCSlib, `exists_iid_gaussian_matrix`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Existence of a Gaussian matrix with independent entries. Let $k \ge 1$ and $d \ge 0$ be integers. Then there is a probability space $(\Omega,
\mathcal{F}, \mu)$ carrying a measurable map $\omega \mapsto A(\omega)$, valued in the
$k \times d$ real matrices, with the following properties: each entry $A_{ij}$, for $1
\le i \le k$ and $1 \le j \le d$, has law $\mathcal{N}(0, 1/k)$ (mean zero and variance
$1/k$); for each row index $i$ the family of entries $(A_{ij})_{j}$ is jointly
independent; and the family of rows $\bigl((A_{ij})_{j}\bigr)_{i}$ is jointly
independent.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- For `k > 0` and any `d`, there exist a probability space `(Ω, μ)` and a measurable random `k × d` matrix `A` on it whose entries `A ω i j` each have law `N(0, 1/k)`, are mutually independent within each row, and whose rows (as `ℝ^d`-valued random variables) are mutually independent — the iid-Gaussian variant of the random projections of [DG03] and [Ver18, §5.3], realized on a concrete sample space. **Proof sketch.** Step 1: on the nested product space `Fin k → Fin d → ℝ` with measure `⊗ᵢ ⊗ⱼ N(0, 1/k)`, the law of the `i`-th row `ω ↦ ω i` is the inner product measure `⊗ⱼ N(0, 1/k)` (`measurePreserving_eval`). Step 2: take this space, this measure, and `A ω i j = ω i j`. Step 3: `A` is measurable, being built from coordinate projections. Step 4: the entry `ω ↦ ω i j` is the `j`-th coordinate of the `i`-th row, so its law is the `j`-th marginal of the inner product measure, namely `N(0, 1/k)`. Step 5: within row `i`, the entries are independent because the joint law of `(ω i j)ⱼ` is the inner product measure (Step 1), which is also the product of the entry marginals (Step 4) (`iIndepFun_iff_map_fun_eq_pi_map`). Step 6: the rows are independent as coordinates of the outer product measure (`iIndepFun_pi`). -/
lemma exists_iid_gaussian_matrix (hk_pos : 0 < k) (d : ℕ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (μ : Measure Ω)
      (_ : IsProbabilityMeasure μ)
      (A : Ω → Matrix (Fin k) (Fin d) ℝ),
      Measurable A ∧
      (∀ (i : Fin k) (j : Fin d),
        Measure.map (fun ω => A ω i j) μ =
          gaussianReal 0 ⟨1 / k, by positivity⟩) ∧
      (∀ i : Fin k, iIndepFun (fun (j : Fin d) ω => A ω i j) μ) ∧
      iIndepFun (fun (i : Fin k) (ω : Ω) (j : Fin d) => A ω i j) μ := by
  -- Sample space: `Fin k → Fin d → ℝ` with nested product Gaussian measure.
  set σ : NNReal := ⟨1 / k, by positivity⟩
  -- Step 1: marginal of the i-th row is the inner product measure
  -- `Measure.pi (fun _ => gaussianReal 0 σ)` (used by the entry-marginal and
  -- within-row-iid bullets below).
  have hrow : ∀ i : Fin k, Measure.map (fun (ω : Fin k → Fin d → ℝ) => ω i)
      (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)))
      = Measure.pi (fun _ : Fin d => gaussianReal 0 σ) := fun i =>
    (MeasureTheory.measurePreserving_eval (μ := fun _ : Fin k =>
      Measure.pi (fun _ : Fin d => gaussianReal 0 σ)) i).map_eq
  -- Step 2: the sample space, the nested product measure, and `A ω i j = ω i j`.
  refine ⟨Fin k → Fin d → ℝ, inferInstance,
    Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)),
    inferInstance,
    fun ω i j => ω i j,
    ?_, ?_, ?_, ?_⟩
  · -- Step 3: `A` is measurable.
    exact measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
      (measurable_pi_apply j).comp (measurable_pi_apply i)
  · -- Step 4: entry marginal: each `(ω i j)` has law `gaussianReal 0 σ`.
    intro i j
    -- Compose the two coordinate projections.
    -- Marginal of the j-th coord of the i-th row is `gaussianReal 0 σ`.
    have hcoord : Measure.map (fun (r : Fin d → ℝ) => r j)
        (Measure.pi (fun _ : Fin d => gaussianReal 0 σ)) = gaussianReal 0 σ :=
      (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin d => gaussianReal 0 σ) j).map_eq
    -- Compose: map (ω ↦ ω i j) = (map (ω ↦ ω i)) ∘ (map (r ↦ r j)).
    have : (fun (ω : Fin k → Fin d → ℝ) => ω i j) =
        (fun (r : Fin d → ℝ) => r j) ∘ (fun ω => ω i) := rfl
    rw [this, ← Measure.map_map (measurable_pi_apply j) (measurable_pi_apply i),
        hrow i, hcoord]
  · -- Step 5: within-row entries iid: for each i, `iIndepFun (j ↦ ω i j)` under the
    -- outer pi.
    intro i
    -- Each entry marginal is `gaussianReal 0 σ` (via the hoisted row marginal `hrow i`).
    have hentry_marginal : ∀ j : Fin d, Measure.map
        (fun (ω : Fin k → Fin d → ℝ) => ω i j)
        (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)))
        = gaussianReal 0 σ := by
      intro j
      have heq : (fun (ω : Fin k → Fin d → ℝ) => ω i j) =
          (fun (r : Fin d → ℝ) => r j) ∘ (fun ω => ω i) := rfl
      rw [heq, ← Measure.map_map (measurable_pi_apply j) (measurable_pi_apply i),
          hrow i]
      exact (MeasureTheory.measurePreserving_eval
        (μ := fun _ : Fin d => gaussianReal 0 σ) j).map_eq
    -- Use `iIndepFun_iff_map_fun_eq_pi_map`: it suffices to check the joint = product.
    rw [iIndepFun_iff_map_fun_eq_pi_map
      (fun j => Measurable.aemeasurable (by fun_prop))]
    -- LHS: joint distribution of (j ↦ ω i j) is `Measure.pi (fun _ => σ)` (= the i-th row).
    have hLHS : Measure.map (fun (ω : Fin k → Fin d → ℝ) (j : Fin d) => ω i j)
        (Measure.pi (fun _ : Fin k => Measure.pi (fun _ : Fin d => gaussianReal 0 σ)))
        = Measure.pi (fun _ : Fin d => gaussianReal 0 σ) := by
      have hfn : (fun (ω : Fin k → Fin d → ℝ) (j : Fin d) => ω i j) = fun ω => ω i := rfl
      rw [hfn, hrow i]
    rw [hLHS]
    -- RHS: product of marginals is also `Measure.pi (fun _ => σ)`.
    congr 1
    funext j
    exact (hentry_marginal j).symm
  · -- Step 6: rows iid: outer pi's `iIndepFun_pi`.
    exact iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id)
