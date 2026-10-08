import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign
import AFTD.Kb.Tcs.DecisionTree

/-!
# DecisionTree.coeffs

Topic: circuits   Node: 7702113aeef2

Provenance: formalization of a published result. Source: TCSlib, `DecisionTree.coeffs`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

The coefficient function $\mathrm{coeffs}\,T : \mathcal{P}(\mathrm{Fin}\,n) \to \bbr$
defined by structural recursion on $T$. A leaf labelled $b$ assigns
$\mathrm{boolToSign}(b)$ to the empty frequency and $0$ to all others; a branch on
variable $i$ with subtrees $\mathrm{lo}, \mathrm{hi}$ assigns to $S$ the value
\[
\frac{\mathrm{coeffs}\,\mathrm{lo}\,S + \mathrm{coeffs}\,\mathrm{hi}\,S}{2}
+ \frac{\mathrm{coeffs}\,\mathrm{lo}\,(S \triangle \{i\})
      - \mathrm{coeffs}\,\mathrm{hi}\,(S \triangle \{i\})}{2}.
\]
-/

open BooleanAnalysis in
variable {n : ℕ} in
/-- The Fourier coefficients of `signEval`, computed by structural recursion. A branch on variable `i` satisfies `f = (f_lo + f_hi)/2 + χ_i (f_lo − f_hi)/2`, and multiplication by `χ_i` shifts frequency `S` to `S ∆ {i}`. -/
noncomputable def DecisionTree.coeffs : DecisionTree n → Finset (Fin n) → ℝ
  | .leaf b, S => if S = ∅ then boolToSign b else 0
  | .branch i lo hi, S =>
      (coeffs lo S + coeffs hi S) / 2
        + (coeffs lo (symmDiff S {i}) - coeffs hi (symmDiff S {i})) / 2
