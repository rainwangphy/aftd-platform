import AFTD.Prelude

/-!
# ErrorCorrectingCodes.Codeword

Topic: information   Node: 9b1472c55444

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

A codeword of length $n$ over alphabet $\alpha$ is a function $c : \mathrm{Fin}\,n \to \alpha$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- A codeword of block-length `n` over alphabet `α`. Concretely, a function `Fin n → α`. -/
abbrev ErrorCorrectingCodes.Codeword (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] := (i : Fin n) → α
