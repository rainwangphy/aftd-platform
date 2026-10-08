import AFTD.Prelude

/-!
# CodingTheory.Johnson.Euc

Topic: information   Node: 784c75fc76db

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.Euc`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Abbreviation for the $n$-dimensional real Euclidean space $\mathbb{R}^n$ with the
$\ell^2$ inner product, i.e.\ \texttt{EuclideanSpace} $\mathbb{R}$ $(\mathrm{Fin}\,n)$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable abbrev CodingTheory.Johnson.Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)
