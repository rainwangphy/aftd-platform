import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProj

/-!
# CodingTheory.Johnson.orthProj_ne_zero

Topic: information   Node: d9da065d5af0

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.orthProj_ne_zero`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Nonvanishing of the projection off a unit vector. Let $u$ and $v$ be unit vectors in a real inner product space, and suppose that $v \neq
u$ and $v \neq -u$. Then the projection of $v$ onto the orthogonal complement of
$\mathrm{span}\{u\}$, namely $v - \langle u,v\rangle\, u$, is nonzero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
open Classical in
open scoped RealInnerProductSpace in
open scoped InnerProductSpace in
open Finset in
open Classical in
attribute [local instance] Classical.dec in
lemma CodingTheory.Johnson.orthProj_ne_zero {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hne1 : v ≠ u) (hne2 : v ≠ -u) :
    orthProj u v ≠ 0 := by
      -- Assume for contradiction that $v - ⟪u, v⟫ • u = 0$.
      by_contra h_contra
      have h_eq : v = (inner ℝ u v) • u := by
        exact eq_of_sub_eq_zero h_contra;
      -- Taking norms on both sides, we get $1 = |⟪u, v⟫|$.
      have h_norm : |(inner ℝ u v)| = 1 := by
        replace h_eq := congr_arg Norm.norm h_eq ; simp_all +decide [ norm_smul ] ;
      rcases eq_or_eq_neg_of_abs_eq h_norm with ( h | h ) <;> simp +decide [ h ] at h_eq ⊢ <;> tauto;
/-
PROVIDED SOLUTION
First show orthProj_inner: ⟪proj v, proj w⟫ = ⟪v,w⟫ - ⟪u,v⟫·⟪u,w⟫ by expanding the inner product bilinearly (unfold orthProj, use inner_sub_left/right, inner_smul_left/right, and ‖u‖=1). Then: ⟪v,w⟫ ≤ 0, and ⟪u,v⟫ = ⟪v,u⟫ ≤ 0, ⟪u,w⟫ = ⟪w,u⟫ ≤ 0 (by real_inner_comm), so ⟪u,v⟫·⟪u,w⟫ ≥ 0. Result ≤ 0 by nlinarith.
-/
