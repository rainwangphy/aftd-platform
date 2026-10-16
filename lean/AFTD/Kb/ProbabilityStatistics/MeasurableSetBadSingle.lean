import AFTD.Prelude
import AFTD.Kb.ProbabilityStatistics.BadSingle
import AFTD.Kb.ProbabilityStatistics.InstMeasurableSpaceMatrixFinRealTCSlib

/-!
# measurableSet_badSingle

Topic: concentration   Node: bb12adf0df8c

Provenance: helper lemma. TCSlib, `measurableSet_badSingle`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/Main.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Measurability of the single-vector distortion event. Fix a vector $x\in\bbr^d$ and a real number $\varepsilon$, and let
$(\Omega,\mathcal{F})$ be a measurable space. Suppose $A\colon\Omega\to\bbr^{k\times d}$
is a measurable map assigning to each $\omega$ a $k\times d$ real matrix $A(\omega)$.
Then the set of outcomes on which $x$ is badly distorted,
\[
\bigl\{\,\omega\in\Omega \;:\; \varepsilon\,\|x\|^2 < \bigl|\,\|A(\omega)\,x\|^2 -
\|x\|^2\,\bigr|\,\bigr\},
\]
is measurable.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real NNReal Matrix Finset in
variable {d k : ℕ} in
/-- For a measurable random matrix `A` and any fixed `x ∈ ℝ^d` and `ε`, the bad event `{ω | BadSingle ε (A ω) x} = {ω | ε‖x‖² < |‖A ω x‖² − ‖x‖²|}` is a measurable set. **Proof sketch.** Step 1: each entry `ω ↦ A ω i j` is measurable (a coordinate projection of the measurable `A`). Step 2: each coordinate of the projection, `ω ↦ (A ω x) i = Σⱼ A ω i j · x j`, is measurable as a finite sum. Step 3: the squared norm `‖A ω x‖² = Σᵢ ((A ω x) i)²` is measurable as a finite sum of squares. Step 4: the event is the strict inequality between the constant `ε‖x‖²` and the measurable function `|‖A ω x‖² − ‖x‖²|`, hence measurable (`measurableSet_lt`). -/
lemma measurableSet_badSingle
    {Ω : Type*} [MeasurableSpace Ω]
    (A : Ω → Matrix (Fin k) (Fin d) ℝ) (hA : Measurable A)
    (x : EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    MeasurableSet {ω | BadSingle ε (A ω) x} := by
  -- `BadSingle ε M x` is `ε * ‖x‖² < |‖M.toEuclideanLin x‖² - ‖x‖²|`.
  -- Each entry (A ω) i j = (A ω).get i j is measurable in ω.
  -- Hence M ↦ (M.toEuclideanLin x) i = ∑ j, M i j * x j is measurable.
  -- Hence ‖M.toEuclideanLin x‖² = ∑ i, ((M.toEuclideanLin x) i)² is measurable.
  -- The full predicate is then `measurable_lt` applied to constant and measurable fns.
  -- Step 1: each entry is measurable.
  have hentries : ∀ i j, Measurable (fun ω => (A ω) i j) := fun i j =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hA)
  -- Step 2: each coordinate of the projection is a finite sum of entries times constants.
  have hmulvec : ∀ i, Measurable (fun ω => (A ω).toEuclideanLin x i) := by
    intro i
    -- (toEuclideanLin M) x i = ∑ j, M i j * x j (via `toLin'` / `mulVec` def)
    have heq : (fun ω => (A ω).toEuclideanLin x i) =
        fun ω => ∑ j, (A ω) i j * x j := by
      funext ω
      change ((A ω).toEuclideanLin x : Fin k → ℝ) i = _
      rfl
    rw [heq]
    exact Finset.measurable_sum _ (fun j _ => (hentries i j).mul_const _)
  -- Step 3: the squared norm is a finite sum of squares of the coordinates.
  have hnorm_sq : Measurable (fun ω => ‖(A ω).toEuclideanLin x‖ ^ 2) := by
    have heq : (fun ω => ‖(A ω).toEuclideanLin x‖ ^ 2) =
        fun ω => ∑ i, ((A ω).toEuclideanLin x i) ^ 2 := by
      funext ω
      rw [EuclideanSpace.norm_eq]
      rw [Real.sq_sqrt (by positivity)]
      simp [sq_abs]
    rw [heq]
    exact Finset.measurable_sum _ (fun i _ => (hmulvec i).pow_const _)
  -- Step 4: the event is a strict inequality between a constant and a measurable function.
  have hdiff : Measurable (fun ω => |‖(A ω).toEuclideanLin x‖ ^ 2 - ‖x‖ ^ 2|) :=
    (hnorm_sq.sub measurable_const).abs
  exact measurableSet_lt measurable_const hdiff
