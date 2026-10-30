import AFTD.Prelude
import AFTD.Kb.Tcs.GroupIsDci

/-!
# group_cayley_digraph_iso_of_mulEquiv

Topic: graphs   Node: 8501dd7cfd0b

Provenance: helper lemma. arXiv:2610.33692, Sec. 1 (the obvious direction of the DCI property)

For any group G, subset S of G and group automorphism σ of G, the Cayley digraphs Cay(G,S) and Cay(G,σ(S)) are isomorphic: there is a bijection f : G ≃ G (namely σ) with x⁻¹ * y ∈ S iff (f x)⁻¹ * f y ∈ σ '' S for all x y.
-/

theorem group_cayley_digraph_iso_of_mulEquiv {G : Type*} [Group G] (S : Set G) (σ : G ≃* G) :
    ∃ f : G ≃ G, ∀ x y : G, (x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ σ '' S) := by
  refine ⟨σ.toEquiv, fun x y => ?_⟩
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
  rw [← map_inv, ← map_mul]
  exact σ.injective.mem_set_image.symm
