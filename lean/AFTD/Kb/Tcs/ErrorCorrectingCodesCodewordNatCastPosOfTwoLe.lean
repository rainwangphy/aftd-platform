import AFTD.Prelude

/-!
# ErrorCorrectingCodes.Codeword.natCast_pos_of_two_le

Topic: information   Node: 211b1b4d0a86

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.natCast_pos_of_two_le`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Positivity of a natural number at least two. Let $q$ be a natural number with $q \ge 2$. Then its image in the real numbers satisfies
$0 < q$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- If `q ≥ 2`, then `q` is positive as a real number. -/
lemma ErrorCorrectingCodes.Codeword.natCast_pos_of_two_le {q : ℕ} (hq : 2 ≤ q) : (0 : ℝ) < q := by
  exact_mod_cast lt_of_lt_of_le zero_lt_two hq
