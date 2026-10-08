import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight

/-!
# Bonami.moment_eq_expect

Topic: combinatorics   Node: 7056472d12dd

Provenance: helper lemma. TCSlib, `Bonami.moment_eq_expect`. Lean proof by Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean (Apache-2.0); 1 verbatim; compiled here.

Moments equal expectations under the uniform law. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function of arity $n$, let $p$ be a natural
number, and let $P$ be a probability measure on the Boolean hypercube $\{0,1\}^n$ that
assigns to each singleton $\{x\}$ the uniform weight $2^{-n}$. Then the $p$-th moment of
$f$ under $P$ equals the expectation of $f^p$ under the uniform measure:
\[
  \int f^p \, dP \;=\; \E\!\left[f^p\right] \;=\; 2^{-n}\sum_{x\in\{0,1\}^n} f(x)^p.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real in
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] in
/-- Identifies finite-space moments under a uniform measure with combinatorial expectations. **Source:** [OD14, Cor. 9.6 (uniform-measure specialization)]. -/
lemma Bonami.moment_eq_expect {n : ℕ} (f : BooleanFunc n) (p : ℕ)
    (P : Measure (BoolCube n)) [IsProbabilityMeasure P]
    (hP_unif : ∀ x, (P {x}).toReal = uniformWeight n) :
    moment f p P = expect (fun x ↦ f x ^ p) := by
  rw [moment]
  simp only [Pi.pow_apply, Integrable.of_finite, integral_fintype, smul_eq_mul]
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  have h_meas_x : (P.real {x}) = uniformWeight n := hP_unif x
  rw [h_meas_x]
