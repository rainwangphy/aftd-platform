import AFTD.Prelude

/-!
# graph_hom_density

Topic: graphs   Node: 376cb86d8aea

Provenance: formalization of a published result. Source: arXiv:2610.13820, Section 1

The homomorphism density q(F, G) of a graph F in a graph G is the number of graph homomorphisms from F to G divided by |V(G)|^{|V(F)|}.
-/

open Classical in
/-- The homomorphism density q(F, G) of a graph F in a graph G. -/
noncomputable def graph_hom_density {α β : Type*} [Fintype α] [Fintype β]
    (F : SimpleGraph α) (G : SimpleGraph β) : ℝ := (Fintype.card (F →g G) : ℝ) / ((Fintype.card β : ℝ) ^ Fintype.card α)
