import AFTD.Prelude
import AFTD.Kb.Tcs.Krawtchouk

/-!
# krawtchouk_zero

Topic: information   Node: 6a382d107d96

Provenance: helper lemma. TCSlib, `krawtchouk_zero`. Lean proof by Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/MRRW.lean (Apache-2.0); 1 verbatim; compiled here.

Value of the zeroth Krawtchouk polynomial. For all natural numbers $n$ and $x$, the degree-zero binary Krawtchouk polynomial is
identically $1$; that is,
\[
  K_0^{(n)}(x) = 1.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
set_option maxHeartbeats 800000 in
theorem krawtchouk_zero (n x : ℕ) : krawtchouk n 0 x = 1 := by
  -- By definition of Krawtchouk polynomials, we know that $K_0^{(n)}(x) = 1$ for all $x$. This follows directly from the definition.
  simp [krawtchouk]

/-
**Lemma 2 (special value at zero)** from the source file.
For every `0 ≤ j ≤ n`, `K_j(0) = C(n,j)`. When `x = 0`, only the `i = 0` term
survives because `C(0, i) = 0` for `i > 0`.
-/
