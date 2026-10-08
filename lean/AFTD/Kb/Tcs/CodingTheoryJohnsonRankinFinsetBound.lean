import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonEuc
import AFTD.Kb.Tcs.CodingTheoryJohnsonRankinBoundGeneral

/-!
# CodingTheory.Johnson.rankin_finset_bound

Topic: information   Node: 1cdf9d464c92

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.rankin_finset_bound`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Rankin bound for pairwise obtuse unit vectors. Let $S$ be a finite set of vectors in the Euclidean space $\bbr^n$, each of norm $1$,
such that any two distinct vectors $u, v \in S$ satisfy $\langle u, v\rangle \le 0$.
Then $\abs{S} \le 2n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
open Classical in
open scoped RealInnerProductSpace in
open scoped InnerProductSpace in
open Finset in
theorem CodingTheory.Johnson.rankin_finset_bound
    {n : ℕ} (S : Finset (Euc n))
    (hunit : ∀ u ∈ S, ‖u‖ = 1)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → ⟪u, v⟫_[ℝ] ≤ 0) :
    S.card ≤ 2 * n := by
  convert rankin_bound_general S _ _ ; aesop;
  · assumption;
  · norm_num [ RCLike.wInner ] at * ; aesop;
