import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProj

/-!
# CodingTheory.Johnson.orthProj_mem_orthogonal

Topic: information   Node: d2e7cb42de78

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.orthProj_mem_orthogonal`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 adapted; compiled here.

Projection off a unit vector lands in the orthogonal complement. Let $V$ be a real inner product space, and let $u,v \in V$ with $\norm{u} = 1$. Then the
vector $v - \langle u,v\rangle\, u$ lies in the orthogonal complement
$(\mathrm{span}_{\bbr}\{u\})^{\perp}$ of the line spanned by $u$.
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
lemma CodingTheory.Johnson.orthProj_mem_orthogonal {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v : V) (hu : ‖u‖ = 1) :
    orthProj u v ∈ (Submodule.span ℝ {u})ᗮ := by
      intro x hx
      obtain ⟨k, rfl⟩ : ∃ k : ℝ, x = k • u := by
        exact Submodule.mem_span_singleton.mp hx |> Exists.imp fun k hk => hk.symm
      simp [orthProj] at *;
      simp +decide [ inner_sub_right, inner_smul_left, inner_smul_right ];
      rw [hu]; ring
/-
PROVIDED SOLUTION
If v - ⟪u,v⟫•u = 0, then v = ⟪u,v⟫•u. Taking norms: 1 = |⟪u,v⟫|·1, so |⟪u,v⟫| = 1, meaning v = u or v = -u, contradiction.
-/
