import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword

/-!
# ErrorCorrectingCodes.Codeword.sub

Topic: information   Node: d8b30a4663b1

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.sub`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Pointwise subtraction of two codewords.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- Pointwise subtraction of two codewords. -/
@[simp]
def ErrorCorrectingCodes.Codeword.sub (c₁ c₂ : Codeword n α) : Codeword n α := fun i ↦ (c₁ i - c₂ i)
