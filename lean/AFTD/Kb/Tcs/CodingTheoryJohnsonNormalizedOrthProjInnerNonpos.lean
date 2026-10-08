import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProj
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProjInnerNonpos

/-!
# CodingTheory.Johnson.normalized_orthProj_inner_nonpos

Topic: information   Node: 2a3906ff6d86

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.normalized_orthProj_inner_nonpos`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Non-positive inner product of normalized projections off a unit vector. Let $u,v,w$ be vectors in a real inner product space with $\norm{u}=1$, and suppose the
three inner products $\langle v,w\rangle$, $\langle v,u\rangle$, and $\langle
w,u\rangle$ are all nonpositive. For a vector $x$, write $x^{\perp}=x-\langle
u,x\rangle\,u$ for its component orthogonal to $u$, and assume that both $v^{\perp}$ and
$w^{\perp}$ are nonzero. Then their normalizations still have nonpositive inner product:
\[
\left\langle \frac{v^{\perp}}{\norm{v^{\perp}}},\
\frac{w^{\perp}}{\norm{w^{\perp}}}\right\rangle \le 0.
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
lemma CodingTheory.Johnson.normalized_orthProj_inner_nonpos {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v w : V) (hu : ‖u‖ = 1)
    (hvw : inner ℝ v w ≤ 0) (hvu : inner ℝ v u ≤ 0) (hwu : inner ℝ w u ≤ 0)
    (_hv_ne : orthProj u v ≠ 0) (_hw_ne : orthProj u w ≠ 0) :
    inner ℝ (‖orthProj u v‖⁻¹ • orthProj u v)
            (‖orthProj u w‖⁻¹ • orthProj u w) ≤ 0 := by
  simp only [inner_smul_left, inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _))
    (mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (norm_nonneg _))
      (orthProj_inner_nonpos u v w hu hvw hvu hwu))
