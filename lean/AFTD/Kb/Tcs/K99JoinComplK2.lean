import AFTD.Prelude

/-!
# k99_join_compl_k2

Topic: graphs   Node: f4af3484ecc3

Provenance: formalization of a published result. Source: arXiv:2611.09347 Definition 1 -- A Structural Lower Bound for the Ramsey Number of the Petersen Graph

The complete bipartite join graph K_{9,9} ∨ Compl(K_2) has vertex set Fin 9 ⊕ Fin 9 ⊕ Fin 2, where the first two parts of size 9 induce a complete bipartite graph K_{9,9}, and the third part consists of two isolated vertices joined to all vertices of the bipartite graph.
-/

/-- The complete bipartite join graph K_{9,9} ∨ K_2ᶜ on Fin 9 ⊕ Fin 9 ⊕ Fin 2. -/
def k99_join_compl_k2 : SimpleGraph (Fin 9 ⊕ Fin 9 ⊕ Fin 2) where
  Adj
    | Sum.inl _, Sum.inr (Sum.inl _) => True
    | Sum.inr (Sum.inl _), Sum.inl _ => True
    | Sum.inr (Sum.inr _), Sum.inl _ => True
    | Sum.inl _, Sum.inr (Sum.inr _) => True
    | Sum.inr (Sum.inr _), Sum.inr (Sum.inl _) => True
    | Sum.inr (Sum.inl _), Sum.inr (Sum.inr _) => True
    | _, _ => False
  symm := ⟨by
    rintro (u | (u | u)) (v | (v | v)) <;> simp⟩
  loopless := ⟨by
    rintro (u | (u | u)) <;> simp⟩
