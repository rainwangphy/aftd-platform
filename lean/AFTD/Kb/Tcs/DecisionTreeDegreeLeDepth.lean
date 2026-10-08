import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisHasDegreeAtMost
import AFTD.Kb.Tcs.DecisionTree
import AFTD.Kb.Tcs.DecisionTreeDepth
import AFTD.Kb.Tcs.DecisionTreeCoeffsEqZeroOfDepthLt
import AFTD.Kb.Tcs.DecisionTreeFourierCoeffSignEval
import AFTD.Kb.Tcs.DecisionTreeSignEval

/-!
# DecisionTree.degree_le_depth

Topic: circuits   Node: 3e45ea73a0c0

Provenance: helper lemma. TCSlib, `DecisionTree.degree_le_depth`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Fourier degree of a decision tree is at most its depth. Let $T$ be a decision tree on $n$ Boolean variables, and let $f\colon\{0,1\}^n\to\bbr$
be the $\pm 1$-valued function it computes, so that $f(x)=\sigma(T(x))$ where $\sigma$
sends $\mathrm{false}$ to $1$ and $\mathrm{true}$ to $-1$. Then $f$ has Fourier degree
at most the depth of $T$: for every $S\subseteq\{1,\dots,n\}$ with $\hat f(S)\ne 0$, one
has $\abs{S}\le\operatorname{depth}(T)$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open BooleanAnalysis in
variable {n : ℕ} in
/-- **Proposition 3.16, degree bound**: a function computed by a decision tree of depth `k` has Fourier degree at most `k`. **Source:** [OD14, Prop. 3.16]. -/
theorem DecisionTree.degree_le_depth (T : DecisionTree n) :
    has_degree_at_most T.signEval T.depth := by
  intro S hS
  by_contra hcard
  push_neg at hcard
  exact hS (by rw [fourierCoeff_signEval]; exact coeffs_eq_zero_of_depth_lt T S hcard)
