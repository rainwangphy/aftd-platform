import AFTD.Prelude
import AFTD.Kb.Tcs.G

/-!
# rows_indep

Topic: concentration   Node: 84ffaa7a5d22

Provenance: helper lemma. TCSlib, `rows_indep`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/RowDistribution.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Independence of coordinates of a random matrix–vector product. Let $(\Omega,\mu)$ be a probability space, and let $A$ be a random $k\times d$ real
matrix, that is, a measurable map assigning to each $\omega\in\Omega$ a matrix
$A(\omega)\in\bbr^{k\times d}$. Suppose the rows of $A$ are mutually independent,
meaning the $k$ random vectors
$\omega\mapsto\bigl(A(\omega)_{i,1},\dots,A(\omega)_{i,d}\bigr)\in\bbr^{d}$, for
$i=1,\dots,k$, are mutually independent under $\mu$. Then for every fixed $x\in\bbr^{d}$
the $k$ coordinates of the product $A(\omega)\,x$, namely the real-valued random
variables $\omega\mapsto (A(\omega)\,x)_i=\sum_{j=1}^{d}A(\omega)_{i,j}\,x_j$ for
$i=1,\dots,k$, are mutually independent under $\mu$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- **Rows of `Ax` are independent.** Given that the row vectors of the random matrix `A` are mutually independent as `(Fin d → ℝ)`-valued random variables, the scalar row-projections `(A ω).toEuclideanLin x i = ∑ⱼ A ω i j · x j` are mutually independent across `i` for every fixed vector `x` — they are measurable functions of disjoint row vectors. This is the independence-of-coordinates observation of [DG03, §2] in the iid-Gaussian-matrix setting (cf. [Ver18, §5.3]). -/
lemma rows_indep
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ)
    (hRowsIndep : iIndepFun (fun (i : Fin k) (ω : Ω) (j : Fin d) => A ω i j) μ)
    (x : EuclideanSpace ℝ (Fin d)) :
    iIndepFun (fun (i : Fin k) ω => (A ω).toEuclideanLin x i) μ := by
  -- Apply `iIndepFun.comp` with the measurable per-row scalar product
  -- `g i := fun (r : Fin d → ℝ) ↦ ∑ j, r j * x j`.
  let g : Fin k → (Fin d → ℝ) → ℝ := fun _ r => ∑ j, r j * x j
  have hg : ∀ i, Measurable (g i) := fun _ =>
    Finset.measurable_sum _ (fun j _ => (measurable_pi_apply j).mul_const _)
  -- `(g i) ∘ (fun ω j => A ω i j) = fun ω => (A ω).toEuclideanLin x i`
  -- by definition of `toEuclideanLin` (a sum).
  exact hRowsIndep.comp g hg
