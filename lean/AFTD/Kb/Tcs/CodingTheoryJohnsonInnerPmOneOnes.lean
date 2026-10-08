import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonOnes
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOne
import AFTD.Kb.Tcs.CodingTheoryJohnsonWt
import AFTD.Kb.Tcs.CodingTheoryJohnsonOnesApply
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOneApplyFalse
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOneApplyTrue
import AFTD.Kb.Tcs.Wt

/-!
# CodingTheory.Johnson.inner_pmOne_ones

Topic: information   Node: 7d4bb4852ede

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.inner_pmOne_ones`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Inner product of the ±1 embedding with the all-ones vector. Let $x$ be a binary word of length $n$, and let $s(x) \in \bbr^n$ denote its $\pm1$
embedding, the vector whose $i$-th coordinate is $-1$ at each position where $x_i$ is
set and $+1$ elsewhere. Writing $\mathbf{1}$ for the all-ones vector and
$\mathrm{wt}(x)$ for the Hamming weight of $x$ (the number of positions at which $x$ is
set), the $\ell^2$ inner product satisfies
\[
\langle s(x), \mathbf{1} \rangle = n - 2\,\mathrm{wt}(x).
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.inner_pmOne_ones {n : ℕ} (x : BitVec n) :
    ⟪pmOne x, ones⟫_[ℝ] = (n : ℝ) - 2 * (wt x : ℝ) := by
  have h_inner_expanded : RCLike.wInner 1 (CodingTheory.Johnson.pmOne x) CodingTheory.Johnson.ones = ∑ i, (pmOne x i) * (ones i) := by
    simp [RCLike.wInner];
  have h_sum_simplified : ∑ i, (pmOne x i) * (ones i) = ∑ i, (if x i then -1 else 1 : ℝ) := by
    exact Finset.sum_congr rfl fun i _ => by unfold CodingTheory.Johnson.pmOne CodingTheory.Johnson.ones; aesop;
  simp_all +decide [ Finset.sum_ite ];
  rw [ show ( Finset.univ.filter fun i => x i = Bool.false ) = Finset.univ \ ( Finset.univ.filter fun i => x i = Bool.true ) by ext; aesop, Finset.card_sdiff ] ; norm_num ; ring_nf!;
  rw [ Nat.cast_sub ( show _ ≤ _ from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] ; ring;
