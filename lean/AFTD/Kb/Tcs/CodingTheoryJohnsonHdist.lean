import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec

/-!
# CodingTheory.Johnson.hdist

Topic: information   Node: bf12171d2acc

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.hdist`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

For binary words $x,y$ of length $n$, the Hamming distance is the number of
coordinates on which they differ:
$\mathrm{hdist}(x,y) = \abs{\{\, i : x_i \neq y_i \,\}}$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable def CodingTheory.Johnson.hdist {n : ℕ} (x y : BitVec n) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card
