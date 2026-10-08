import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisHasDegreeAtMost
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BonamiDegreeZeroConst
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc

/-!
# Bonami.degree_zero_fourth_moment

Topic: combinatorics   Node: 460daa018de8

Provenance: helper lemma. TCSlib, `Bonami.degree_zero_fourth_moment`. Lean proof by Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean (Apache-2.0); 1 verbatim; compiled here.

Fourth moment of a degree-zero Boolean function. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function of degree at most $0$, meaning that every
set $S$ with a nonzero Fourier coefficient $\hat f(S)\ne 0$ satisfies $|S|\le 0$. Then,
with expectations taken under the uniform measure on $\{0,1\}^n$,
\[
  \E[f^4] \;=\; \bigl(\E[f^2]\bigr)^2.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real in
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] in
/-- Computes the fourth moment of a degree-zero Boolean function from its second moment. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.degree_zero_fourth_moment {n : ℕ} (f : BooleanFunc n) (hf : has_degree_at_most f 0) :
    expect (fun x => f x ^ 4) = (expect (fun x => f x ^ 2)) ^ 2 := by
  -- Since $f$ is constant, we have $f(x) = f(default)$ for all $x$.
  have h_const : ∀ x : BoolCube n, f x = f default := by
    exact fun x => degree_zero_const f hf x;
  unfold expect; simp +decide [ h_const ] ; ring_nf;
  unfold uniformWeight; norm_num [ pow_mul ] ; ring_nf;
  simp [ pow_mul' ]
