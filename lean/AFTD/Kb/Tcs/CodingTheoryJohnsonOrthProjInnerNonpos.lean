import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProj

/-!
# CodingTheory.Johnson.orthProj_inner_nonpos

Topic: information   Node: dbf455c5f31f

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.orthProj_inner_nonpos`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Projection off a unit vector preserves nonpositive inner products. Let $V$ be a real inner product space, and let $u,v,w \in V$ with $\norm{u} = 1$.
Suppose the three pairwise inner products $\langle v,w\rangle$, $\langle v,u\rangle$,
and $\langle w,u\rangle$ are all nonpositive. For a vector $x \in V$, write $x - \langle
u,x\rangle\, u$ for the projection of $x$ onto the orthogonal complement of
$\mathrm{span}\{u\}$. Then the projections of $v$ and $w$ again have nonpositive inner
product:
\[
\bigl\langle\, v - \langle u,v\rangle\, u,\ \ w - \langle u,w\rangle\, u \,\bigr\rangle
\le 0.
\]
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
lemma CodingTheory.Johnson.orthProj_inner_nonpos {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v w : V) (hu : ‖u‖ = 1)
    (hvw : inner ℝ v w ≤ 0) (hvu : inner ℝ v u ≤ 0) (hwu : inner ℝ w u ≤ 0) :
    inner ℝ (orthProj u v) (orthProj u w) ≤ 0 := by
      have huu : ⟪u, u⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hu]; norm_num
      unfold orthProj; simp +decide [ *, inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right ] ; ring_nf; (
      nlinarith [ real_inner_comm u w, real_inner_comm v u, huu ]);
