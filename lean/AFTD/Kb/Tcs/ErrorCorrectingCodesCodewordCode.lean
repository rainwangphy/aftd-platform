import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword

/-!
# ErrorCorrectingCodes.Codeword.Code

Topic: information   Node: 916711ea2cbd

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.Code`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

A (block) code of length $n$ over $\alpha$ is a finite set (\texttt{Finset}) of codewords.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- A code of block-length `n` over `α`: a finite set of codewords. -/
abbrev ErrorCorrectingCodes.Codeword.Code (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := Finset (Codeword n α)
