import AFTD.Prelude

/-!
# CodingTheory.Johnson.alpha

Topic: information   Node: 06f0317fec7c

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.alpha`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

The real quantity
\[
\alpha(n,d) \;=\; \sqrt{\frac{n - 2d}{n}}.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable def CodingTheory.Johnson.alpha (n d : ℕ) : ℝ :=
  Real.sqrt ((((n : ℝ) - 2 * (d : ℝ)) / (n : ℝ)))
