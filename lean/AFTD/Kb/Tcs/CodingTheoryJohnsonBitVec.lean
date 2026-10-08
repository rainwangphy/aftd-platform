import AFTD.Prelude

/-!
# CodingTheory.Johnson.BitVec

Topic: information   Node: 1eaf9a038c98

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.BitVec`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

The type of binary words of length $n$, namely functions $\mathrm{Fin}\,n \to \mathrm{Bool}$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable abbrev CodingTheory.Johnson.BitVec (n : ℕ) := Fin n → Bool
