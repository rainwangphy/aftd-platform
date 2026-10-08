import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance

/-!
# ErrorCorrectingCodes.Codeword.hamming_ball

Topic: information   Node: a2bccba45301

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.hamming_ball`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

The Hamming ball of radius $l$ around $c$:
\[
B_l(c) = \{c' : d(c',c) \le l\},
\]
implemented as a \texttt{Finset}.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- The Hamming ball of radius `l` centred at codeword `c`: the set of codewords within Hamming distance `l` of `c`. -/
@[simp]
def ErrorCorrectingCodes.Codeword.hamming_ball (l : ℕ) (c : Codeword n α) : Finset (Codeword n α) :=
  {c' : Codeword n α | hamming_distance c' c ≤ l}.toFinset
