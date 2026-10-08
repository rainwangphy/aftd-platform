import AFTD.Prelude

/-!
# ErrorCorrectingCodes.Codeword.one_sub_pos_of_lt_one

Topic: information   Node: f1d903b171c9

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.one_sub_pos_of_lt_one`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Positivity of one minus a subunital real. Let $p$ be a real number with $p < 1$. Then $1 - p > 0$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- If `p < 1`, then `1 - p` is positive. -/
lemma ErrorCorrectingCodes.Codeword.one_sub_pos_of_lt_one {p : ℝ} (hp : p < 1) : 0 < 1 - p := by
  exact sub_pos.mpr hp
