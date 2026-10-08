import AFTD.Prelude
import AFTD.Kb.Tcs.Krawtchouk

/-!
# krawtchouk_one

Topic: information   Node: 53ad9764fab3

Provenance: helper lemma. TCSlib, `krawtchouk_one`. Lean proof by Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/MRRW.lean (Apache-2.0); 1 verbatim; compiled here.

Value of the first Krawtchouk polynomial. Let $n$ and $x$ be natural numbers with $x \le n$. Then the first binary Krawtchouk
polynomial at $x$ satisfies
\[
  K_1^{(n)}(x) = n - 2x.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
set_option maxHeartbeats 800000 in
theorem krawtchouk_one (n x : ℕ) (hx : x ≤ n) :
    krawtchouk n 1 x = (n : ℝ) - 2 * (x : ℝ) := by
  unfold krawtchouk;
  norm_num [ Finset.sum_range_succ, hx ] ; ring

/-
**Lemma 1 (generating function)** from the source file.
For every `x ∈ {0,...,n}`,
  `∑_{j=0}^{n} K_j(x) · z^j = (1 - z)^x · (1 + z)^{n-x}`.
-/
