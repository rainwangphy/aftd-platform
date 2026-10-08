import AFTD.Prelude

/-!
# binaryEntropy

Topic: information   Node: 2ae2e451729b

Provenance: formalization of a published result. Source: TCSlib, `binaryEntropy`. Lean proof by Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/MRRW.lean (Apache-2.0); 1 verbatim; compiled here.

The binary entropy function
\[
  H(x) \;=\; -x\log_2 x - (1-x)\log_2(1-x),
\]
using the base-$2$ logarithm, with the convention $0\log_2 0 = 0$ inherited from
$\log_2 0 = 0$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
set_option maxHeartbeats 800000 in
/-- **Definition 3 (binary entropy)** from the source file. `binaryEntropy x = -x · log₂(x) - (1-x) · log₂(1-x)`, with the convention `0 · log₂ 0 = 0` (which holds automatically since `Real.logb 2 0 = 0` in Mathlib). Note: this uses base-2 logarithm (`Real.logb 2`), unlike Mathlib's `Real.binEntropy` which uses natural logarithm. -/
noncomputable def binaryEntropy (x : ℝ) : ℝ :=
  -x * Real.logb 2 x - (1 - x) * Real.logb 2 (1 - x)
