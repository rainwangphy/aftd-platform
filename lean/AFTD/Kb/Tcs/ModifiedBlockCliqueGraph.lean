import AFTD.Prelude

/-!
# modified_block_clique_graph

Topic: graphs   Node: 75adfb64d487

Provenance: formalization of a published result. Source: arXiv:2611.05762 Sec 6.9

The modified block-clique graph K_v^*(D) of a block design with blocks indexed by B and points in X has vertex set X ⊕ (B × Fin k), with clique edges between local vertices of the same block and matching edges between local vertices and their corresponding points.
-/

/-- The modified block-clique graph K_v^*(D) of a block design on vertex set X ⊕ (B × Fin k). -/
def modified_block_clique_graph {X B : Type*} {k : ℕ} (block_pts : B → Fin k → X) :
    SimpleGraph (X ⊕ (B × Fin k)) where
  Adj
    | Sum.inl _, Sum.inl _ => False
    | Sum.inl x, Sum.inr ⟨b, j⟩ => block_pts b j = x
    | Sum.inr ⟨b, j⟩, Sum.inl x => block_pts b j = x
    | Sum.inr ⟨b1, j1⟩, Sum.inr ⟨b2, j2⟩ => b1 = b2 ∧ j1 ≠ j2
  symm := ⟨by
    intro u v h
    rcases u with x | ⟨b1, j1⟩ <;> rcases v with y | ⟨b2, j2⟩
    · exact False.elim h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by
    intro u h
    rcases u with x | ⟨b, j⟩
    · exact h
    · exact h.2 rfl⟩
