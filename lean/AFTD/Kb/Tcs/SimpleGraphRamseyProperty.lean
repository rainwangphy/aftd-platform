import AFTD.Prelude

/-!
# simple_graph_ramsey_property

Topic: combinatorics   Node: 014b98c26a59

Provenance: formalization of a published result. Source: arXiv:2610.36522

simple_graph_ramsey_property F H N holds if every simple graph G on N vertices contains a copy of F or its complement Gᶜ contains a copy of H.
-/

/-- The 2-color Ramsey property for graphs F, H on N vertices. -/
def simple_graph_ramsey_property {α β : Type*} (F : SimpleGraph α) (H : SimpleGraph β) (N : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin N), F.IsContained G ∨ H.IsContained Gᶜ
