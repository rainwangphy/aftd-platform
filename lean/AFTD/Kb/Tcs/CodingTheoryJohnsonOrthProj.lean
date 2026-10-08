import AFTD.Prelude

/-!
# CodingTheory.Johnson.orthProj

Topic: information   Node: 3554a242ab3c

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.orthProj`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

For $u,v$ in a real inner product space, $\mathrm{orthProj}(u,v) = v - \langle u,v\rangle u$,
the projection of $v$ onto the orthogonal complement of $\mathrm{span}\{u\}$.
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
/-- Orthogonal projection onto the complement of span {u}. -/
noncomputable def CodingTheory.Johnson.orthProj {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u : V) (v : V) : V :=
  v - (inner ℝ u v) • u
/-
PROVIDED SOLUTION
Introduce x ∈ span {u}, get x = k•u via Submodule.mem_span_singleton. Then ⟪k•u, v - ⟪u,v⟫•u⟫ = k(⟪u,v⟫ - ⟪u,v⟫·⟪u,u⟫) = 0 since ⟪u,u⟫ = ‖u‖² = 1.
-/
