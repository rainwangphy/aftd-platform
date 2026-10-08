import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProj
import AFTD.Kb.Tcs.CodingTheoryJohnsonMkProj

/-!
# CodingTheory.Johnson.mkProj_val

Topic: information   Node: 7f35b8472ccf

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.mkProj_val`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Underlying vector of the normalized projection. Let $V$ be a real inner product space, let $u \in V$ be a unit vector, and let $v \in
V$. Write $w = v - \langle u, v\rangle\, u$ for the component of $v$ orthogonal to $u$.
The normalized vector $\norm{w}^{-1} w$, regarded as an element of the orthogonal
complement $(\mathrm{span}_{\bbr}\{u\})^{\perp}$ of the line spanned by $u$, has
underlying vector in $V$ equal to $\norm{w}^{-1} w$.
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
lemma CodingTheory.Johnson.mkProj_val {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) (hu : ‖u‖ = 1) (v : V) :
    ((mkProj u hu v : (↑(Submodule.span ℝ {u})ᗮ)) : V) = ‖orthProj u v‖⁻¹ • orthProj u v := rfl
