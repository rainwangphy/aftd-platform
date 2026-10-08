import AFTD.Prelude

/-!
# ErrorCorrectingCodes.Codeword.lt_one_of_le_one_sub_inv

Topic: information   Node: ef56ab416d39

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.lt_one_of_le_one_sub_inv`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

A rate bound below one. Let $q$ and $p$ be real numbers with $q > 0$. If $p \le 1 - 1/q$, then $p < 1$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- If `q > 0` and `p ≤ 1 - 1/q`, then `p < 1`. -/
lemma ErrorCorrectingCodes.Codeword.lt_one_of_le_one_sub_inv {q : ℝ} {p : ℝ} (hq : 0 < q) (hp : p ≤ 1 - 1 / q) : p < 1 := by
  have h_inv_pos : 0 < 1 / q := one_div_pos.mpr hq
  linarith
