import AFTD.Prelude

/-!
# b4_graph

Topic: graphs   Node: a4d0acedaedf

Provenance: formalization of a published result. Source: arXiv:2610.21388, Section 2

The graph B_4(n_0, n_1, n_2, n_3) on the disjoint union of four complete blocks of sizes n_0, n_1, n_2, n_3, with edges between blocks 0 and 1, blocks 1 and 3, and blocks 2 and 3.
-/

/-- The graph B_4(n_0, n_1, n_2, n_3) of arXiv:2610.21388: generalized lexicographic product of G_4 = P_4 with complete graphs of sizes n_i. -/
def b4_graph (n : Fin 4 → ℕ) : SimpleGraph (Σ i : Fin 4, Fin (n i)) :=
  { Adj := fun x y => x ≠ y ∧ (x.1 = y.1 ∨ (x.1 = 0 ∧ y.1 = 1) ∨ (x.1 = 1 ∧ y.1 = 0) ∨
      (x.1 = 1 ∧ y.1 = 3) ∨ (x.1 = 3 ∧ y.1 = 1) ∨ (x.1 = 2 ∧ y.1 = 3) ∨ (x.1 = 3 ∧ y.1 = 2)),
    symm := ⟨fun x y h => ⟨h.1.symm, by
      rcases h.2 with h | ⟨h0, h1⟩ | ⟨h1, h0⟩ | ⟨h1, h3⟩ | ⟨h3, h1⟩ | ⟨h2, h3⟩ | ⟨h3, h2⟩
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr (Or.inl ⟨h1, h0⟩))
      · exact Or.inr (Or.inl ⟨h0, h1⟩)
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3, h1⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, h3⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, h2⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h2, h3⟩)))))⟩⟩,
    loopless := ⟨fun x h => h.1 rfl⟩ }
