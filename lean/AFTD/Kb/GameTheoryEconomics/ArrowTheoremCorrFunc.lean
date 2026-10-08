import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff

/-!
# ArrowTheorem.corrFunc

Topic: social_choice   Node: fff736426845

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.corrFunc`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{Fourier correlation function} of $f$ is
\[
  \mathrm{corr}(f) \;=\; \sum_{S\subseteq[n]} \hat f(S)^2\,(-1/3)^{|S|}.
\]
For odd $f$, only odd-level terms contribute.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- The pairwise correlation function: ∑_S f̂(S)² · (-1/3)^|S|. For odd f, only odd-level terms are nonzero. **Source:** [OD14, Ch. 2]. -/
noncomputable def ArrowTheorem.corrFunc (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n), fourierCoeff f S ^ 2 * (-1/3 : ℝ) ^ S.card
