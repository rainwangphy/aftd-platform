import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisHasDegreeAtMost
import AFTD.Kb.Tcs.BonamiBonamiExpect
import AFTD.Kb.Tcs.BonamiMomentEqExpect
import AFTD.Kb.Tcs.BonamiUniformMeasure
import AFTD.Kb.Tcs.BonamiUniformMeasureApply
import AFTD.Kb.Tcs.BonamiIsBReasonable
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc
import AFTD.Kb.Tcs.BonamiInstIsProbabilityMeasureBoolCubeUniformMeasure

/-!
# Bonami.bonami_lemma

Topic: combinatorics   Node: b916b0152f6b

Provenance: formalization of a published result. Source: Bonami's hypercontractivity lemma for low-degree functions, as formalized in TCSlib (`Bonami.bonami_lemma`). Lean proof by Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean (Apache-2.0); 1 verbatim; compiled here.

Bonami's hypercontractivity lemma for low-degree functions. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function whose Fourier expansion has degree at
most $k$; that is, every nonzero Fourier coefficient $\hat f(S)$ is supported on a set
$S$ with $\abs{S} \le k$. When $\{0,1\}^n$ is equipped with the uniform probability
measure, $f$ is $9^k$-reasonable: its fourth moment is controlled by the square of its
second moment via
\[
\E[f^4] \le 9^k \bigl(\E[f^2]\bigr)^2 .
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real in
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] in
/-- Shows that a degree-`k` Boolean function is `9^k`-reasonable under the uniform measure. This is the uniform-bit specialization of the stated corollary. **Source:** [OD14, Cor. 9.6]. -/
lemma Bonami.bonami_lemma {n : ℕ} (k : ℕ) (f : BooleanFunc n)
    (hf : has_degree_at_most f k) :
    IsBReasonable f (uniformMeasure n) ((9 : ℝ) ^ k) := (by
  refine ⟨inferInstance, one_le_pow₀ (by norm_num), MemLp.of_discrete, ?_⟩
  rw [moment_eq_expect f 4 (uniformMeasure n) uniformMeasure_apply]
  rw [moment_eq_expect f 2 (uniformMeasure n) uniformMeasure_apply]
  exact bonami_expect k f hf
)
