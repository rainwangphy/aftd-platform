import AFTD.Prelude

/-!
# BooleanAnalysis.boolToSign

Topic: combinatorics   Node: 14b3b5897662

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.boolToSign`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{sign encoding} maps $\mathrm{Bool}$ to $\{-1,1\}\subset\bbr$:
\[
  \sigma(b) \;=\; \begin{cases} 1 & b = \texttt{false},\\
                                -1 & b = \texttt{true}. \end{cases}
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Converts a `Bool` to `{-1, 1} ⊆ ℝ`: `false ↦ 1`, `true ↦ -1`. **Source:** [OD14, §1.1]. -/
def BooleanAnalysis.boolToSign (b : Bool) : ℝ := if b then -1 else 1
