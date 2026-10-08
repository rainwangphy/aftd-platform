import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonAlpha

/-!
# CodingTheory.Johnson.alpha_nonneg

Topic: information   Node: c963bb518d56

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.alpha_nonneg`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Nonnegativity of the shift parameter. For all natural numbers $n$ and $d$, the shift parameter $\alpha(n,d) = \sqrt{(n -
2d)/n}$ satisfies $0 \le \alpha(n,d)$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.alpha_nonneg (n d : ℕ) : 0 ≤ alpha n d := by
  exact Real.sqrt_nonneg _
