import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword

/-!
# ErrorCorrectingCodes.Codeword.add

Topic: information   Node: 0a92c0f82f94

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.add`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Pointwise addition of two codewords.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- Pointwise addition of two codewords. -/
@[simp]
def ErrorCorrectingCodes.Codeword.add (c₁ c₂ : Codeword n α) : Codeword n α := fun i ↦ (c₁ i + c₂ i)
