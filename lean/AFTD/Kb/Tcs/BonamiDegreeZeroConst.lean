import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisHasDegreeAtMost
import AFTD.Kb.Tcs.BooleanAnalysisWalshExpansion
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignFalse
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignTrue
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignSq
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignMulSelf
import AFTD.Kb.Tcs.BooleanAnalysisChiSSingleton
import AFTD.Kb.Tcs.BooleanAnalysisSumBoolToSign
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf
import AFTD.Kb.Tcs.BooleanAnalysisFlipBitFlipBit
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSignNot
import AFTD.Kb.Tcs.BooleanAnalysisInstAddCommGroupBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisInstModuleRealBooleanFunc

/-!
# Bonami.degree_zero_const

Topic: combinatorics   Node: e415fae7d6b5

Provenance: helper lemma. TCSlib, `Bonami.degree_zero_const`. Lean proof by Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Hypercontractivity/Bonami.lean (Apache-2.0); 1 adapted; compiled here.

Degree-zero Boolean functions are constant. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function of degree at most $0$; that is, every set
$S$ with nonzero Fourier--Walsh coefficient $\hat f(S)\ne 0$ satisfies $|S|\le 0$. Then
$f$ is constant: for every point $x\in\{0,1\}^n$ one has $f(x)=f(x_0)$, where $x_0$ is
the all-$\mathtt{false}$ point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
open MeasureTheory Set Filter ProbabilityTheory BooleanAnalysis Real in
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] in
/-- Shows that a Boolean function of Fourier degree zero is constant. **Source:** [OD14, Cor. 9.6 (proof)]. -/
lemma Bonami.degree_zero_const {n : ℕ} (f : BooleanFunc n) (hf : has_degree_at_most f 0) :
    ∀ x, f x = f default := by
  intro x;
  -- By definition of $f$, we can write it as a sum of its Fourier coefficients.
  have h_fourier : f = fun x => ∑ S : Finset (Fin n), BooleanAnalysis.fourierCoeff f S * chiS S x := by
    exact funext fun x => walsh_expansion f x;
  rw [ h_fourier ];
  refine' Finset.sum_congr rfl fun S hS => _;
  by_cases h : BooleanAnalysis.fourierCoeff f S = 0
  · simp only [h, zero_mul]
  have hS : S = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp (hf S h))
  subst hS
  simp [BooleanAnalysis.chiS]
