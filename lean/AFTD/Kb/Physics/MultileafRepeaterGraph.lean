import AFTD.Prelude

/-!
# multileaf_repeater_graph

Topic: quantum_mechanics   Node: 6c8a68df0016

Provenance: formalization of a published result. Source: arXiv:2603.23892, Section 3 and Appendix C

For a natural number k and a block size function n : Fin k → ℕ, the multi-leaf repeater graph on vertex type Σ i : Fin k, Fin (n i) is the simple graph where two distinct vertices are adjacent if and only if they are distinct core vertices (both having local index 0), or they belong to the same block and at least one is the core vertex (has local index 0).
-/

/-- The multi-leaf repeater graph with k core vertices and block sizes n. -/
def multileaf_repeater_graph {k : ℕ} (n : Fin k → ℕ) :
    SimpleGraph ((i : Fin k) × Fin (n i)) where
  Adj p q := p ≠ q ∧
    ((p.1 ≠ q.1 ∧ p.2.val = 0 ∧ q.2.val = 0) ∨
     (p.1 = q.1 ∧ (p.2.val = 0 ∨ q.2.val = 0)))
  symm := ⟨fun p q h => by
    rcases h with ⟨hne, ⟨h1, h2, h3⟩ | ⟨h1, h2⟩⟩
    · exact ⟨hne.symm, Or.inl ⟨h1.symm, h3, h2⟩⟩
    · exact ⟨hne.symm, Or.inr ⟨h1.symm, h2.symm⟩⟩⟩
  loopless := ⟨fun p h => h.1 rfl⟩
