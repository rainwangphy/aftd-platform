import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOne
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOneApplyFalse

/-!
# CodingTheory.Johnson.pmOne_apply_true

Topic: information   Node: 669a34c992db

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.pmOne_apply_true`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Value of the ±1 embedding at a true coordinate. Let $x$ be a binary word of length $n$, and let $s(x) \in \bbr^n$ denote its $\pm1$
embedding, whose $i$-th coordinate is $-1$ when $x_i$ is true and $+1$ when $x_i$ is
false. Then for every index $i$ with $x_i$ true, the $i$-th coordinate of $s(x)$ equals
$-1$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
@[simp] lemma CodingTheory.Johnson.pmOne_apply_true {n : ℕ} (x : BitVec n) (i : Fin n) (h : x i = true) :
    pmOne x i = (-1 : ℝ) := by
  simp [pmOne, h]
