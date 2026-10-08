import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword

/-!
# ErrorCorrectingCodes.Codeword.zero

Topic: information   Node: a379683dcc60

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.zero`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Pointwise addition, subtraction, and the all-zero codeword.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- The all-zeros codeword. -/
@[simp]
def ErrorCorrectingCodes.Codeword.zero : Codeword n α := fun (_ : Fin n) ↦ 0
