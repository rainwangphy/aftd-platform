import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisHasDegreeAtMost
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.BonamiAvgLast
import AFTD.Kb.Tcs.BonamiRestrictLast
import AFTD.Kb.Tcs.BonamiSumBoolCubeSucc
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc

/-!
# Bonami.degree_avgLast

Topic: combinatorics   Node: 3718320e4bff

Provenance: helper lemma. TCSlib, `Bonami.degree_avgLast`. Lean proof by Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Decomposition.lean (Apache-2.0); 1 adapted; compiled here.

Averaging over a coordinate preserves the degree bound. Let $f\colon\{0,1\}^{n+1}\to\bbr$ be a Boolean function on $n+1$ variables, and suppose
$f$ has degree at most $k$; that is, every set $S$ with nonzero Fourier coefficient
$\hat f(S)\ne 0$ satisfies $\abs{S}\le k$. Form the average of $f$ over its last
coordinate, the function on $n$ variables obtained by fixing that coordinate to each of
its two values and averaging,
\[
  x \;\longmapsto\; \tfrac12\bigl(f(x,0) + f(x,1)\bigr).
\]
Then this averaged function also has degree at most $k$: each set $S$ with a nonzero
Fourier coefficient of the average satisfies $\abs{S}\le k$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
/-- Shows that final-coordinate averaging preserves an upper bound on Fourier degree. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.degree_avgLast {n : ℕ} (f : BooleanFunc (n + 1)) (k : ℕ)
    (hf : has_degree_at_most f k) :
    has_degree_at_most (avgLast f) k := by
  intro S hS_nonzero
  have h_fourier_coeff :
      BooleanAnalysis.fourierCoeff (avgLast f) S =
        BooleanAnalysis.fourierCoeff f (S.image Fin.castSucc) := by
    unfold BooleanAnalysis.fourierCoeff avgLast
    unfold innerProduct restrictLast
    unfold expect
    have h_expand :
        ∑ x : BoolCube (n + 1), f x * chiS (Finset.image Fin.castSucc S) x =
          ∑ x : BoolCube n,
            (f (Fin.snoc x false) * chiS (Finset.image Fin.castSucc S) (Fin.snoc x false) +
             f (Fin.snoc x true) * chiS (Finset.image Fin.castSucc S) (Fin.snoc x true)) := by
      convert sum_boolCube_succ _
      rw [Finset.sum_add_distrib]
    simp_all +decide [Finset.sum_add_distrib, add_mul, mul_add, div_mul_eq_mul_div,
      Finset.mul_sum _ _ _]
    rw [← Finset.sum_add_distrib]
    refine' Finset.sum_congr rfl fun x hx => _
    unfold uniformWeight
    ring_nf
    unfold chiS
    simp +decide [Finset.prod_image]
    ring
  have := hf (Finset.image Fin.castSucc S)
  simp_all +decide [Finset.card_image_of_injective _ (Fin.castSucc_injective _)]
