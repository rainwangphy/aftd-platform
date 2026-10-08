import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword

/-!
# ErrorCorrectingCodes.Codeword.hamming_distance

Topic: information   Node: 61c8750edae0

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.hamming_distance`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Hamming distance between two codewords, wrapping Mathlib's \texttt{hammingDist}.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- The Hamming distance between two codewords. -/
def ErrorCorrectingCodes.Codeword.hamming_distance (c1 c2 : Codeword n α) : ℕ :=
  hammingDist c1 c2
