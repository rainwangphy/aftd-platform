import AFTD.Prelude

/-!
# group_is_dci

Topic: graphs   Node: 08c22008a97e

Provenance: formalization of a published result. Source: arXiv:2610.33692 (On the isomorphism problem of Cayley digraphs), Sec. 1, definition of a DCI-group

For a group G (any type with a Group instance; G explicit), group_is_dci G is the Prop: for all subsets S T : Set G, if there exists a bijection f : G ≃ G such that for all x y : G, (x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T) -- an isomorphism of the Cayley digraphs Cay(G,S) and Cay(G,T), where x → y is an arc when x⁻¹ * y lies in the connection set -- then there exists a group automorphism σ : G ≃* G with σ '' S = T (the image of S under σ is T).
-/

/-- `G` is a DCI-group: whenever the Cayley digraphs `Cay(G,S)` and `Cay(G,T)` (arc `x → y` iff `x⁻¹ * y` lies in the connection set) are isomorphic via a bijection `f : G ≃ G`, some group automorphism `σ : G ≃* G` maps `S` onto `T`. -/
def group_is_dci (G : Type*) [Group G] : Prop :=
  ∀ S T : Set G, (∃ f : G ≃ G, ∀ x y : G, (x⁻¹ * y ∈ S ↔ (f x)⁻¹ * f y ∈ T)) →
    ∃ σ : G ≃* G, σ '' S = T
