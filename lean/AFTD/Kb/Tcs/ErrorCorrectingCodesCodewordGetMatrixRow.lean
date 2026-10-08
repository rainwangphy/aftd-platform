import AFTD.Prelude

/-!
# ErrorCorrectingCodes.Codeword.get_matrix_row

Topic: information   Node: 3a044bf18dd8

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.get_matrix_row`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/LinearCodes.lean (Apache-2.0); 1 verbatim; compiled here.

Utility: extract row `i` of matrix `M` as a `1×k` matrix.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k m : ℕ} in
/-- Utility: extract row `i` of matrix `M` as a `1×k` matrix. -/
def ErrorCorrectingCodes.Codeword.get_matrix_row (n k : ℕ) (M : Matrix (Fin n) (Fin k) α) (i : Fin n) :
    Matrix (Fin 1) (Fin k) α :=
  Matrix.of (fun _ j => (M i) j)
