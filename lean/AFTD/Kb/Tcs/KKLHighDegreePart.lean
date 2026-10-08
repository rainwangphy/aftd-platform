import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff

/-!
# KKL.highDegreePart

Topic: combinatorics   Node: a73596a2f356

Provenance: formalization of a published result. Source: TCSlib, `KKL.highDegreePart`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{high-degree part} of $f$ at level $k$ keeps only the Fourier coefficients
of degree strictly greater than $k$:
\[
  f_{>k}(x) \;=\; \sum_{\abs{S} > k} \hat f(S)\,\chi_S(x).
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
/-- The high-degree part of `f`: Fourier coefficients at levels `> k`. `f_{>k}(x) = sum_{|S| > k} fhat(S) * chi_S(x)`. **Source:** [OD14, Ch. 10]. -/
noncomputable def KKL.highDegreePart (f : BooleanFunc n) (k : ℕ) : BooleanFunc n :=
  fun x => ∑ S : Finset (Fin n),
    if k < S.card then fourierCoeff f S * chiS S x else 0
