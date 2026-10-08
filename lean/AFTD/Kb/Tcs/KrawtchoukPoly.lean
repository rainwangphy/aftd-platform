import AFTD.Prelude

/-!
# krawtchoukPoly

Topic: information   Node: 972fdec983da

Provenance: formalization of a published result. Source: TCSlib, `krawtchoukPoly`. Lean proof by Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/MRRW.lean (Apache-2.0); 1 verbatim; compiled here.

The family of real polynomials defined by the three-term recurrence
$K_0 = 1$, $K_1 = n - 2X$, and
\[
  (j+2)\,K_{j+2} \;=\; (n - 2X)\,K_{j+1} - (n-j)\,K_j,
\]
extending the integer-argument definition to real arguments.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
set_option maxHeartbeats 800000 in
/-- **Krawtchouk polynomials as actual polynomials over ℝ** (following the suggestion of Remark 1 from the source file). Defined via the three-term recurrence: - `K_0(x) = 1` - `K_1(x) = n - 2x` - `(j+2) · K_{j+2}(x) = (n - 2x) · K_{j+1}(x) - (n - j) · K_j(x)` This extends Definition 4 to real arguments as actual polynomials, enabling use where real-valued arguments are needed (e.g., the Christoffel–Darboux identity). -/
noncomputable def krawtchoukPoly (n : ℕ) : ℕ → Polynomial ℝ
  | 0 => 1
  | 1 => Polynomial.C (n : ℝ) - 2 * Polynomial.X
  | (j + 2) =>
    ((Polynomial.C (n : ℝ) - 2 * Polynomial.X) * krawtchoukPoly n (j + 1) -
     Polynomial.C ((n : ℝ) - ↑j) * krawtchoukPoly n j) *
     Polynomial.C (((j + 2 : ℕ) : ℝ)⁻¹)

/-
`K_0^{(n)}(x) = 1` for all `x`. This is immediate from Definition 4 of the
source file: the sum has only the `i = 0` term, giving
`(-1)^0 · C(x,0) · C(n-x,0) = 1`.
-/
