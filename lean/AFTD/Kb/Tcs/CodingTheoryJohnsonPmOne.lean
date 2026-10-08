import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonEuc

/-!
# CodingTheory.Johnson.pmOne

Topic: information   Node: 241b2a5f6268

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.pmOne`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

The map sending a binary word $x$ to the real vector in $\mathbb{R}^n$ whose $i$-th
coordinate is $-1$ if $x_i = \texttt{true}$ and $+1$ otherwise.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable def CodingTheory.Johnson.pmOne {n : ℕ} (x : BitVec n) : Euc n :=
  WithLp.toLp 2 (fun i => if x i then (-1 : ℝ) else (1 : ℝ))
