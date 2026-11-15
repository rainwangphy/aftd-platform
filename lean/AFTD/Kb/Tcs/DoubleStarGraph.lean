import AFTD.Prelude

/-!
# double_star_graph

Topic: graphs   Node: c2927eb37968

Provenance: formalization of a published result. Source: arXiv:2611.15124 Section 2.2, Domination in token graphs of graphs with domination number two

The double star graph S_{a,b} on vertex set Bool ⊕ Fin a ⊕ Fin b, with centers Sum.inl false and Sum.inl true joined by an edge, and with a leaves attached to Sum.inl false and b leaves attached to Sum.inl true.
-/

/-- The double star S_{a,b} on vertex type Bool ⊕ Fin a ⊕ Fin b. -/
def double_star_graph (a b : ℕ) : SimpleGraph (Bool ⊕ Fin a ⊕ Fin b) := SimpleGraph.fromRel fun x y =>
  (x = Sum.inl false ∧ y = Sum.inl true) ∨
  (∃ i : Fin a, x = Sum.inl false ∧ y = Sum.inr (Sum.inl i)) ∨
  (∃ j : Fin b, x = Sum.inl true ∧ y = Sum.inr (Sum.inr j))
