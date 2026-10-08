import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec

/-!
# CodingTheory.Johnson.wt

Topic: information   Node: 62154f861cbc

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.wt`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

For a binary word $x$ of length $n$, its weight is the number of coordinates where
$x$ takes the value \texttt{true}:
$\mathrm{wt}(x) = \abs{\{\, i : x_i = \texttt{true} \,\}}$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable def CodingTheory.Johnson.wt {n : ℕ} (x : BitVec n) : ℕ :=
  (Finset.univ.filter (fun i => x i = true)).card
