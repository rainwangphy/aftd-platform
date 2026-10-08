import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOne

/-!
# CodingTheory.Johnson.coord_mul_pmOne

Topic: information   Node: 7e5f1b0f1f49

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.coord_mul_pmOne`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Coordinatewise product of $\pm 1$ embeddings. Let $x, y$ be binary words of length $n$, and encode each as a $\pm 1$ vector in
$\bbr^n$ by sending its $i$-th bit to $-1$ when that bit is true and to $+1$ when it is
false. Then for every coordinate $i$, the product of the $i$-th entries of these two
embeddings equals $1$ if $x_i = y_i$ and $-1$ if $x_i \ne y_i$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.coord_mul_pmOne {n : ℕ} (x y : BitVec n) (i : Fin n) :
    (pmOne x i) * (pmOne y i) = if x i = y i then (1 : ℝ) else (-1 : ℝ) := by
  by_cases hx : x i <;> by_cases hy : y i <;> simp [pmOne, hx, hy]
