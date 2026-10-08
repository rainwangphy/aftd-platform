import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisWalshExpansion
import AFTD.Kb.Tcs.KKLHighDegreePart
import AFTD.Kb.Tcs.KKLLowDegreePart

/-!
# KKL.low_plus_high_eq

Topic: combinatorics   Node: 3cdccfa487b2

Provenance: helper lemma. TCSlib, `KKL.low_plus_high_eq`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

Low and high degree parts reconstruct the function. Let $f : \{0,1\}^n \to \bbr$ be a Boolean function and let $k \in \bbn$ be a threshold
level. Then for every point $x \in \{0,1\}^n$ of the cube,
\[
  f_{\le k}(x) + f_{>k}(x) = f(x),
\]
where $f_{\le k}(x) = \sum_{\abs{S}\le k}\hat f(S)\,\chi_S(x)$ and $f_{>k}(x) =
\sum_{\abs{S} > k}\hat f(S)\,\chi_S(x)$ are the low- and high-degree parts of $f$ at
level $k$. That is, splitting the Fourier–Walsh expansion of $f$ into frequencies of
degree at most $k$ and degree greater than $k$ recovers $f$ exactly.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
lemma KKL.low_plus_high_eq (f : BooleanFunc n) (k : ℕ) (x : BoolCube n) :
    lowDegreePart f k x + highDegreePart f k x = f x := by
  simp only [lowDegreePart, highDegreePart]
  rw [← Finset.sum_add_distrib]
  have : ∀ S ∈ (Finset.univ : Finset (Finset (Fin n))),
      (if S.card ≤ k then fourierCoeff f S * chiS S x else 0) +
      (if k < S.card then fourierCoeff f S * chiS S x else 0) =
      fourierCoeff f S * chiS S x := by
    intro S _
    by_cases h : S.card ≤ k
    · simp [h, Nat.not_lt.mpr h]
    · simp [h, Nat.lt_of_not_le h]
  rw [Finset.sum_congr rfl this]
  exact (walsh_expansion f x).symm

-- Step 07: The Fourier coefficient of lowDegreePart is the truncated coefficient.
