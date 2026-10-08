import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonCoordMulPmOne
import AFTD.Kb.Tcs.CodingTheoryJohnsonHdist
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOne

/-!
# CodingTheory.Johnson.inner_pmOne_pmOne

Topic: information   Node: 46f284d448a7

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.inner_pmOne_pmOne`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Inner product of two ±1 embeddings. For any two binary words $x, y$ of length $n$, let $\phi(x), \phi(y) \in \mathbb{R}^n$
be their $\pm 1$ embeddings, whose $i$-th coordinates are $-1$ when the corresponding
bit is true and $+1$ otherwise. Then their Euclidean inner product is
\[
\langle \phi(x),\, \phi(y)\rangle \;=\; n - 2\,d(x,y),
\]
where $d(x,y)$ is the Hamming distance, the number of coordinates on which $x$ and $y$
differ.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.inner_pmOne_pmOne {n : ℕ} (x y : BitVec n) :
    ⟪pmOne x, pmOne y⟫_[ℝ] = (n : ℝ) - 2 * (hdist x y : ℝ) := by
  have h_pmOne : ∀ i, (pmOne x i) * (pmOne y i) = if x i = y i then 1 else -1 := by
    exact fun i => coord_mul_pmOne x y i;
  have h_hdist : (CodingTheory.Johnson.hdist x y : ℝ) = ∑ i, (if x i ≠ y i then 1 else 0) := by
    simp +decide [ Finset.sum_ite ];
    exact congr_arg Finset.card ( Finset.filter_congr fun _ _ => by aesop );
  simp_all +decide [ RCLike.wInner ];
  simp_all +decide [ mul_comm, Finset.sum_ite ];
  rw [ Finset.filter_not, Finset.card_sdiff ] ; norm_num ; ring_nf;
  rw [ Nat.cast_sub ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring
