import AFTD.Prelude

/-!
# CodingTheory.Johnson.J2

Topic: information   Node: d2f41901c97f

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.J2`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

The real quantity
\[
J_2(n,d) \;=\; \frac{n - \sqrt{n\,(n - 2d)}}{2}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable def CodingTheory.Johnson.J2 (n d : ℕ) : ℝ :=
  (((n : ℝ) - Real.sqrt ((n : ℝ) * ((n : ℝ) - 2 * (d : ℝ)))) / 2)
