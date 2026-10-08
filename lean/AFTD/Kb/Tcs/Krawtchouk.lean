import AFTD.Prelude

/-!
# krawtchouk

Topic: information   Node: e06bbaf76eb3

Provenance: formalization of a published result. Source: TCSlib, `krawtchouk`. Lean proof by Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/MRRW.lean (Apache-2.0); 1 verbatim; compiled here.

For naturals $n$, $j$, $x$,
\[
  K_j^{(n)}(x) \;=\; \sum_{i=0}^{j} (-1)^i \binom{x}{i}\binom{n-x}{j-i},
\]
where the subtraction $n-x$ is natural-number subtraction; the definition gives the
intended values for $x \le n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
set_option maxHeartbeats 800000 in
/-- **Definition 4 (binary Krawtchouk polynomials, integer arguments)** from the source file. For `0 ≤ j ≤ n`, the binary Krawtchouk polynomial `K_j^{(n)}(x)` evaluated at `x ∈ {0,1,...,n}` is given by `K_j^{(n)}(x) = ∑_{i=0}^{j} (-1)^i · C(x,i) · C(n-x, j-i)`. This definition uses natural number subtraction; it gives the correct values for `x ≤ n`. -/
noncomputable def krawtchouk (n j x : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (j + 1),
    (-1 : ℝ) ^ i * (Nat.choose x i : ℝ) * (Nat.choose (n - x) (j - i) : ℝ)
