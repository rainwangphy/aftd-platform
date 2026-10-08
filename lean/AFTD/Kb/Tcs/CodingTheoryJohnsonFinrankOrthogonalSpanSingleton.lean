import AFTD.Prelude

/-!
# CodingTheory.Johnson.finrank_orthogonal_span_singleton

Topic: information   Node: 855dbc51a8ba

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.finrank_orthogonal_span_singleton`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Rank of the orthogonal complement of a line. Let $V$ be a finite-dimensional real inner product space, and let $u \in V$ be a unit
vector, so that $\norm{u} = 1$. Then the orthogonal complement of the line
$\mathrm{span}_{\bbr}\{u\}$ has dimension one less than that of $V$:
\[
\dim_{\bbr}\bigl(\mathrm{span}_{\bbr}\{u\}\bigr)^{\perp} = \dim_{\bbr} V - 1.
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
lemma CodingTheory.Johnson.finrank_orthogonal_span_singleton {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (u : V) (hu : ‖u‖ = 1) :
    Module.finrank ℝ (↥(Submodule.span ℝ {u})ᗮ) = Module.finrank ℝ V - 1 := by
  have h1 : Module.finrank ℝ (↥(ℝ ∙ u)) = 1 := by
    apply finrank_span_singleton; intro h; simp [h] at hu
  have := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ u)
  omega
