import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProj
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProjMemOrthogonal

/-!
# CodingTheory.Johnson.mkProj

Topic: information   Node: b0421081a36c

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.mkProj`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Given a unit vector $u$, this packages the normalized projection
$\norm{\mathrm{orthProj}(u,v)}^{-1}\mathrm{orthProj}(u,v)$ together with its membership
proof as an element of the subspace $(\mathrm{span}_{\mathbb{R}}\{u\})^{\perp}$.
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
noncomputable def CodingTheory.Johnson.mkProj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) (hu : ‖u‖ = 1) (v : V) : (↑(Submodule.span ℝ {u})ᗮ) :=
  ⟨‖orthProj u v‖⁻¹ • orthProj u v,
   Submodule.smul_mem _ _ (orthProj_mem_orthogonal u v hu)⟩
