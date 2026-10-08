import AFTD.Prelude

/-!
# ErrorCorrectingCodes.Codeword.qaryEntropy

Topic: information   Node: 15f2568d3760

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.qaryEntropy`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

\[
H_q(p) \;=\; p\log_q(q-1) - p\log_q p - (1-p)\log_q(1-p).
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- The q-ary entropy function `H_q(p) = p·log_q(q-1) - p·log_q(p) - (1-p)·log_q(1-p)`. -/
noncomputable def ErrorCorrectingCodes.Codeword.qaryEntropy (q : ℕ) (p : ℝ) :=
  p * (Real.logb q (q-1)) - p * (Real.logb q p) - (1-p)*(Real.logb q (1 -p))
