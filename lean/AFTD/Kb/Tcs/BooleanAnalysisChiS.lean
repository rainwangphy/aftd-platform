import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign

/-!
# BooleanAnalysis.chiS

Topic: combinatorics   Node: d9eb164de6e1

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.chiS`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{Walsh--Fourier character} associated to $S\subseteq[n]$ is
\[
  \chi_S(x) \;=\; \prod_{i\in S}(-1)^{x_i}
  \;=\; \prod_{i\in S}\sigma(x_i).
\]
The family $\{\chi_S\}_{S\subseteq[n]}$ forms an orthonormal basis for
$L^2(\{0,1\}^n,\mathrm{uniform})$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- The Walsh–Fourier character `χ_S : {0,1}ⁿ → ℝ` associated to a set `S ⊆ [n]`. `χ_S(x) = ∏_{i ∈ S} (-1)^{x_i}`. This forms an orthonormal basis for `L²({0,1}ⁿ, uniform)`. **Source:** [OD14, §1.2]. -/
noncomputable def BooleanAnalysis.chiS (S : Finset (Fin n)) : BooleanFunc n :=
  fun x ↦ ∏ i ∈ S, boolToSign (x i)
