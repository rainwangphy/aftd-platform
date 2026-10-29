import AFTD.Prelude

/-!
# book_graph

Topic: combinatorics   Node: 8416bfd4f265

Provenance: formalization of a published result. Source: arXiv:2610.36522

The book graph B_n is the graph consisting of n triangles sharing a common edge (spine), formalized on vertices Fin 2 ⊕ Fin n.
-/

/-- The book graph B_n is the join K_2 + K_n^c on Fin 2 ⊕ Fin n. -/
def book_graph (n : ℕ) : SimpleGraph (Fin 2 ⊕ Fin n) where
  Adj
  | .inl i, .inl j => i ≠ j
  | .inl _, .inr _ => True
  | .inr _, .inl _ => True
  | .inr _, .inr _ => False
  symm := ⟨by rintro (x | x) (y | y) h <;> simp_all [Ne.symm]⟩
  loopless := ⟨by rintro (x | x) h <;> simp_all⟩
