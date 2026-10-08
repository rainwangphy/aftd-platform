import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProj
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProjNeZero

/-!
# CodingTheory.Johnson.norm_normalized_orthProj

Topic: information   Node: a422ff8ce94d

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.norm_normalized_orthProj`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Normalizing the projection off a unit vector yields a unit vector. Let $u,v$ be unit vectors in a real inner product space, with $v \neq u$ and $v \neq
-u$, and set $w = v - \langle u,v\rangle\, u$, the projection of $v$ onto the orthogonal
complement of $\mathrm{span}\{u\}$. Then the rescaled vector $\norm{w}^{-1}\, w$ has
norm $1$.
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
lemma CodingTheory.Johnson.norm_normalized_orthProj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hne1 : v ≠ u) (hne2 : v ≠ -u) :
    ‖‖orthProj u v‖⁻¹ • orthProj u v‖ = 1 := by
  rw [norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr (orthProj_ne_zero u v hu hv hne1 hne2))]
