import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOne

/-!
# CodingTheory.Johnson.pmOne_apply_false

Topic: information   Node: d57207bd457e

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.pmOne_apply_false`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Value of the $\pm 1$ embedding at a false coordinate. Let $x$ be a binary word of length $n$, and let the $\pm 1$ embedding send $x$ to the
vector in $\bbr^n$ whose $i$-th coordinate is $-1$ when $x_i$ is true and $+1$ when
$x_i$ is false. If the $i$-th entry of $x$ is false, then the $i$-th coordinate of the
embedded vector equals $1$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
@[simp] lemma CodingTheory.Johnson.pmOne_apply_false {n : ℕ} (x : BitVec n) (i : Fin n) (h : x i = false) :
    pmOne x i = (1 : ℝ) := by
  simp [pmOne, h]
