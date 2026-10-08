import AFTD.Prelude
import AFTD.Kb.Tcs.CodeA

/-!
# rate

Topic: information   Node: 7972a707c8e7

Provenance: formalization of a published result. Source: TCSlib, `rate`. Lean proof by Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/MRRW.lean (Apache-2.0); 1 verbatim; compiled here.

For $\delta \in [0,1]$, the asymptotic rate is
\[
  R(\delta) \;=\; \limsup_{n\to\infty} \frac{1}{n}\log_2 A(n, \lfloor \delta n \rfloor).
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
set_option maxHeartbeats 800000 in
/-- **Definition 2 (asymptotic rate)** from the source file. For `δ ∈ [0,1]`, `rate δ = limsup_{n→∞} (1/n) · log₂ A(n, ⌊δn⌋)`. -/
noncomputable def rate (δ : ℝ) : ℝ :=
  Filter.limsup (fun (n : ℕ) =>
    Real.logb 2 ↑(codeA n ⌊δ * ↑n⌋₊) / (n : ℝ)) Filter.atTop
