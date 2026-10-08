import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisHasDegreeAtMost
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BonamiBonamiAlgebra
import AFTD.Kb.Tcs.BonamiDegreeZeroFourthMoment
import AFTD.Kb.Tcs.BonamiAvgLast
import AFTD.Kb.Tcs.BonamiDegreeAvgLast
import AFTD.Kb.Tcs.BonamiDegreeDiffLast
import AFTD.Kb.Tcs.BonamiDiffLast
import AFTD.Kb.Tcs.BonamiExpectCsSq
import AFTD.Kb.Tcs.BonamiExpectFourthNonneg
import AFTD.Kb.Tcs.BonamiExpectSqNonneg
import AFTD.Kb.Tcs.BonamiExpectSqNonnegProd
import AFTD.Kb.Tcs.BonamiFourthMomentDecomp
import AFTD.Kb.Tcs.BonamiSecondMomentDecomp
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc
import AFTD.Kb.Tcs.G

/-!
# Bonami.bonami_expect

Topic: combinatorics   Node: 750183306de4

Provenance: helper lemma. TCSlib, `Bonami.bonami_expect`. Lean proof by Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean (Apache-2.0); 1 verbatim; compiled here.

Bonami inequality in expectation form. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function of degree at most $k$, meaning that
every nonzero Fourier coefficient $\hat f(S)$ is supported on a set $S$ with $|S| \le
k$. Writing $\E$ for the expectation under the uniform measure on $\{0,1\}^n$, we then
have
\[
  \E[f^4] \;\le\; 9^{k}\,\bigl(\E[f^2]\bigr)^2.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real in
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] in
/-- Bounds the fourth moment of a degree-`k` Boolean function by `9^k` times its squared second moment. This is the uniform-bit specialization of the stated corollary. **Source:** [OD14, Cor. 9.6]. -/
lemma Bonami.bonami_expect {n : ℕ} (k : ℕ) (f : BooleanFunc n)
    (hf : has_degree_at_most f k) :
    expect (fun x ↦ f x ^ 4) ≤ (9 : ℝ) ^ k * (expect (fun x ↦ f x ^ 2)) ^ 2 := by
  induction n generalizing k with
  | zero =>
    -- BoolCube 0 has one element, everything reduces to f(default)
    unfold expect;
    norm_num [ Finset.card_univ ] ; ring_nf ; norm_cast; norm_num;
    unfold uniformWeight; norm_num; ring_nf; norm_cast; norm_num;
    exact le_mul_of_one_le_right ( by positivity ) ( one_le_pow₀ ( by norm_num ) )
  | succ n ih =>
    by_cases hk : k = 0
    · -- k = 0: f is constant
      subst hk
      simp only [pow_zero, one_mul]
      exact le_of_eq (degree_zero_fourth_moment f hf)
    · -- k ≥ 1: write k = m + 1
      obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := Nat.exists_eq_succ_of_ne_zero hk
      -- Define g = avgLast f, h = diffLast f
      set g := avgLast f
      set hh := diffLast f
      -- Apply the decompositions
      rw [fourth_moment_decomp f, second_moment_decomp f]
      -- Get degree bounds
      have hg_deg : has_degree_at_most g (m + 1) := degree_avgLast f (m + 1) hf
      have hh_deg : has_degree_at_most hh m := by
        have := degree_diffLast f (m + 1) hf
        simp at this
        exact this
      -- Apply IH
      have hg_bound := ih (m + 1) g hg_deg
      have hh_bound := ih m hh hh_deg
      -- Get non-negativity
      have ha := expect_sq_nonneg g
      have hb := expect_sq_nonneg hh
      have hA := expect_fourth_nonneg g
      have hB := expect_fourth_nonneg hh
      -- Get Cauchy-Schwarz
      have hCS := expect_cs_sq g hh
      -- Apply the algebraic lemma
      set a := expect (fun x => g x ^ 2)
      set b := expect (fun x => hh x ^ 2)
      set A := expect (fun x => g x ^ 4)
      set B := expect (fun x => hh x ^ 4)
      set C := expect (fun x => g x ^ 2 * hh x ^ 2)
      have hC_nn : 0 ≤ C := expect_sq_nonneg_prod g hh
      exact bonami_algebra ha hb hB hC_nn hg_bound hh_bound hCS
