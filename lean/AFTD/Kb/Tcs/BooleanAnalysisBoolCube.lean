import AFTD.Prelude

/-!
# BooleanAnalysis.BoolCube

Topic: combinatorics   Node: 849453744b13

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.BoolCube`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The \emph{Boolean hypercube} of dimension $n$ is $\{0,1\}^n$,
represented as the function type $\mathrm{Fin}\,n \to \mathrm{Bool}$.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
/-- Defines the Boolean hypercube `{0,1}ⁿ`. **Source:** [OD14, §1.1]. -/
abbrev BooleanAnalysis.BoolCube (n : ℕ) := Fin n → Bool
