import AFTD.Prelude

/-!
# subdivided_doubled_complete_graph

Topic: graphs   Node: 6fee66b6100a

Provenance: formalization of a published result. Source: arXiv:2611.17022, Section 2

For every natural number t, the 1-subdivision of the doubled complete multigraph on t vertices is the bipartite simple graph on Fin t ⊕ { p : Fin t × Fin t // p.1 ≠ p.2 } where each vertex (i, j) in the right part is adjacent to x_i and x_j in the left part.
-/

/-- The 1-subdivision of the doubled complete multigraph on t vertices, with parts X = Fin t and Y = {p : Fin t × Fin t // p.1 ≠ p.2}. -/
def subdivided_doubled_complete_graph (t : ℕ) :
    SimpleGraph (Sum (Fin t) { p : Fin t × Fin t // p.1 ≠ p.2 }) := {
  Adj := fun u v => match u, v with
    | Sum.inl i, Sum.inr ⟨(x, y), _⟩ => i = x ∨ i = y
    | Sum.inr ⟨(x, y), _⟩, Sum.inl i => i = x ∨ i = y
    | _, _ => False
  symm := ⟨by rintro (i | ⟨⟨x, y⟩, hne⟩) (j | ⟨⟨x', y'⟩, hne'⟩) h <;> simp_all⟩
  loopless := ⟨by rintro (i | ⟨⟨x, y⟩, hne⟩) <;> simp⟩
}
