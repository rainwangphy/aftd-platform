import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword

/-!
# ErrorCorrectingCodes.Codeword.uniform_vector_dist

Topic: information   Node: 08f00fd789e3

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.uniform_vector_dist`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/LinearCodes.lean (Apache-2.0); 1 verbatim; compiled here.

The uniform probability mass function on $\alpha^n$, encoded as a function
$\alpha^n\to\mathbb{R}$ assigning $1/|\alpha|^n$ to each vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k m : ℕ} in
/-- The uniform distribution on length-`n` vectors: each vector has probability `1/|α|^n`. -/
noncomputable def ErrorCorrectingCodes.Codeword.uniform_vector_dist (n : ℕ) (α : Type*) [Fintype α] [DecidableEq α] :
    (Codeword n α) → ℝ :=
  fun _ => 1 / ((Fintype.card α) ^ n)
