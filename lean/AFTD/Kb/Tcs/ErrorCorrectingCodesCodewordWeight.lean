import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordZero

/-!
# ErrorCorrectingCodes.Codeword.weight

Topic: information   Node: c8c7b3280f8b

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.weight`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The Hamming weight of $c$ is $d(c, \mathbf{0})$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- The Hamming weight of a codeword: its distance from the all-zeros word. -/
def ErrorCorrectingCodes.Codeword.weight (c : Codeword n α) : ℕ := hamming_distance c zero
