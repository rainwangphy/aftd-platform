import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.DecisionTree
import AFTD.Kb.Tcs.DecisionTreeCoeffs
import AFTD.Kb.Tcs.DecisionTreeFourierCoeffSumChiS
import AFTD.Kb.Tcs.DecisionTreeSignEval
import AFTD.Kb.Tcs.DecisionTreeSignEvalEqSumCoeffs
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf

/-!
# DecisionTree.fourierCoeff_signEval

Topic: circuits   Node: 2d8aa917042e

Provenance: helper lemma. TCSlib, `DecisionTree.fourierCoeff_signEval`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Fourier coefficients of a decision tree. Let $T$ be a decision tree on $n$ Boolean variables, and let $\sigma\!\circ\! T$ denote
its sign-encoded function $x \mapsto \sigma(T(x))$ on the Boolean hypercube $\{0,1\}^n$.
Then for every frequency set $S \subseteq [n]$, the Fourier–Walsh coefficient of this
function at $S$ agrees with the recursively defined tree coefficient:
\[
  \widehat{\sigma\!\circ\! T}(S) \;=\; \mathrm{coeffs}(T)(S).
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
variable {n : ℕ} in
/-- The Fourier coefficients of the tree function are exactly `T.coeffs`. -/
theorem DecisionTree.fourierCoeff_signEval (T : DecisionTree n) (S : Finset (Fin n)) :
    fourierCoeff T.signEval S = T.coeffs S := by
  have hrepr : T.signEval = fun x => ∑ S : Finset (Fin n), T.coeffs S * chiS S x :=
    funext fun x => signEval_eq_sum_coeffs T x
  rw [hrepr, fourierCoeff_sum_chiS]
