import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisExpect
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisInnerProduct
import AFTD.Kb.Tcs.BooleanAnalysisParseval
import AFTD.Kb.Tcs.BooleanAnalysisUniformWeight
import AFTD.Kb.Tcs.KKLFourierCoeffLowDegreePart
import AFTD.Kb.Tcs.KKLHighDegreePart
import AFTD.Kb.Tcs.KKLL2DistSq
import AFTD.Kb.Tcs.KKLLowDegreePart
import AFTD.Kb.Tcs.KKLLowPlusHighEq
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf

/-!
# KKL.lowDegree_l2_error

Topic: combinatorics   Node: 310677c06dde

Provenance: helper lemma. TCSlib, `KKL.lowDegree_l2_error`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

$L^2$ error of the low-degree truncation. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function, and for a natural number $k$ let
$f_{\le k}(x) = \sum_{\abs{S}\le k} \hat f(S)\,\chi_S(x)$ be its low-degree part,
retaining only the Fourier--Walsh coefficients of degree at most $k$. Then, under the
uniform measure on the cube, the squared $L^2$ distance between $f$ and this truncation
equals the total Fourier weight sitting above level $k$:
\[
  \E\big[(f(x) - f_{\le k}(x))^2\big] \;=\; \sum_{\abs{S} > k} \hat f(S)^2 .
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
lemma KKL.lowDegree_l2_error (f : BooleanFunc n) (k : ℕ) :
    l2DistSq f (lowDegreePart f k) =
    ∑ S : Finset (Fin n), if k < S.card then fourierCoeff f S ^ 2 else 0 := by
  -- Step 1: f x - lowDegreePart f k x = highDegreePart f k x
  have hfg : ∀ x, f x - lowDegreePart f k x = highDegreePart f k x := by
    intro x; linarith [low_plus_high_eq f k x]
  -- Step 2: l2DistSq = innerProduct (highDegreePart f k) (highDegreePart f k)
  have step2 : l2DistSq f (lowDegreePart f k) =
      innerProduct (highDegreePart f k) (highDegreePart f k) := by
    simp only [l2DistSq, innerProduct, expect]
    congr 1; congr 1; ext x
    rw [hfg x, sq]
  rw [step2, parseval]
  -- Step 3: compute fourierCoeff of highDegreePart
  congr 1; ext S
  have hfour : fourierCoeff (highDegreePart f k) S =
      if k < S.card then fourierCoeff f S else 0 := by
    have hdef : highDegreePart f k = fun x => f x - lowDegreePart f k x :=
      funext (fun x => (hfg x).symm)
    rw [hdef]
    unfold BooleanAnalysis.fourierCoeff innerProduct expect
    rw [show uniformWeight n * ∑ x, (f x - lowDegreePart f k x) * chiS S x =
        uniformWeight n * ∑ x, f x * chiS S x -
        uniformWeight n * ∑ x, lowDegreePart f k x * chiS S x from by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1
      apply Finset.sum_congr rfl; intro x _; ring]
    change fourierCoeff f S - fourierCoeff (lowDegreePart f k) S =
        if k < S.card then fourierCoeff f S else 0
    rw [fourierCoeff_lowDegreePart]
    by_cases h : S.card ≤ k
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_le h]
  rw [hfour]
  split_ifs <;> simp

-- Step 09: Tail Fourier weight bound: sum_{|S|>k} fhat(S)^2 <= I[f] / k.
-- This is the key estimate: levels > k contribute at most I[f]/k to Parseval.
