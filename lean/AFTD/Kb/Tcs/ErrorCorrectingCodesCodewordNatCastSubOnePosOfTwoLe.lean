import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordNatCastOneLtOfTwoLe

/-!
# ErrorCorrectingCodes.Codeword.natCast_sub_one_pos_of_two_le

Topic: information   Node: e052e8cb4eb5

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.natCast_sub_one_pos_of_two_le`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Positivity of $q-1$ for $q \ge 2$. Let $q$ be a natural number with $q \ge 2$. Then, regarded as a real number, $q - 1$ is
strictly positive: $0 < q - 1$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- If `q ≥ 2`, then `q - 1` is positive as a real number. -/
lemma ErrorCorrectingCodes.Codeword.natCast_sub_one_pos_of_two_le {q : ℕ} (hq : 2 ≤ q) : (0 : ℝ) < q - 1 := by
  linarith [show (1 : ℝ) < q from natCast_one_lt_of_two_le hq]
