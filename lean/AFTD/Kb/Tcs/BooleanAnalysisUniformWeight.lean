import AFTD.Prelude

/-!
# BooleanAnalysis.uniformWeight

Topic: combinatorics   Node: 0a898194af8d

Provenance: formalization of a published result. Source: TCSlib, `BooleanAnalysis.uniformWeight`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The uniform probability measure on $\{0,1\}^n$ assigns weight
$2^{-n}$ to each point.
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Defines the uniform probability weight `2⁻ⁿ` on each point of `{0,1}ⁿ`. **Source:** [OD14, §1.1]. -/
noncomputable def BooleanAnalysis.uniformWeight (n : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ n
