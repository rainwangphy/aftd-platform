import AFTD.Prelude

/-!
# ErrorCorrectingCodes.Codeword.natCast_one_lt_of_two_le

Topic: information   Node: a15e3aaf67e6

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.natCast_one_lt_of_two_le`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

One is less than a natural number at least two. For any natural number $q$ with $q \ge 2$, the image of $q$ under the canonical
embedding of the naturals into the reals satisfies $1 < q$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- If `q ≥ 2`, then `q > 1` as a real number. -/
lemma ErrorCorrectingCodes.Codeword.natCast_one_lt_of_two_le {q : ℕ} (hq : 2 ≤ q) : (1 : ℝ) < q := by
  exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hq
