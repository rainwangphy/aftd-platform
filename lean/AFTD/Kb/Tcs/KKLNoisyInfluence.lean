import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff

/-!
# KKL.noisyInfluence

Topic: combinatorics   Node: 209fa76fc4a2

Provenance: formalization of a published result. Source: TCSlib, `KKL.noisyInfluence`. Lean proof by Mina, Owen McGinty, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/KKL.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{noisy influence} of coordinate $i$ on $f$ at noise rate $\rho$ is
\[
  \mathrm{Inf}_i^{\rho}[f] \;=\; \sum_{S \ni i} \rho^{\abs{S}-1}\,\hat f(S)^2,
\]
the sum being taken over all $S \subseteq [n]$ containing $i$.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
open Classical in
/-- The noisy influence of coordinate `i` at noise rate `rho`: `Inf_i^rho[f] = sum_{S ni i} rho^{|S|-1} * fhat(S)^2`. **Source:** [OD14, Ch. 9]. -/
noncomputable def KKL.noisyInfluence (ρ : ℝ) (i : Fin n) (f : BooleanFunc n) : ℝ :=
  ∑ S : Finset (Fin n),
    if i ∈ S then ρ ^ (S.card - 1) * fourierCoeff f S ^ 2 else 0
