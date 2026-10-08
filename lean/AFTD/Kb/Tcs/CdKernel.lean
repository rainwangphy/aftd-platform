import AFTD.Prelude
import AFTD.Kb.Tcs.KrawtchoukPoly

/-!
# cdKernel

Topic: information   Node: 9d71ca47c748

Provenance: formalization of a published result. Source: TCSlib, `cdKernel`. Lean proof by Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/MRRW.lean (Apache-2.0); 1 verbatim; compiled here.

For $t \le n$ and real $a, x$, the truncated reproducing kernel is
\[
  \Phi_{n,t}(a,x) \;=\; \sum_{j=0}^{t} \frac{K_j^{(n)}(a)\,K_j^{(n)}(x)}{\binom{n}{j}}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
set_option maxHeartbeats 800000 in
/-- **Christoffel–Darboux kernel** from Section 3 of the source file. For `t ∈ {0,...,n}` and real parameters `a, x`, the truncated reproducing kernel is `Φ_{n,t}(a,x) = ∑_{j=0}^{t} K_j(a) · K_j(x) / C(n,j)`. -/
noncomputable def cdKernel (n t : ℕ) (a x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (t + 1),
    (krawtchoukPoly n j).eval a * (krawtchoukPoly n j).eval x / (Nat.choose n j : ℝ)

/-
**Proposition 1 (Christoffel–Darboux identity for Krawtchouk)** from the source
file.
For `0 ≤ t ≤ n-1`, there exists a positive scalar `c > 0` such that
  `Φ_{n,t}(a,x) = c · (K_t(a) · K_{t+1}(x) - K_{t+1}(a) · K_t(x)) / (a - x)`
for all real `a ≠ x`.

As noted in Remark 3 of the source file, the precise value of `c` is irrelevant
for the Delsarte application because scaling `F` does not change `F(0)/F_0`.
-/
