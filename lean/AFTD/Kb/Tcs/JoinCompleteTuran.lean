import AFTD.Prelude

/-!
# join_complete_turan

Topic: graphs   Node: 19f3ab11ed98

Provenance: formalization of a published result. Source: arXiv:2610.41371, Section 3.1, eq. (3)

The graph join G_a = K_a ∨ T_{r-1}(n-a) on vertex set Fin a ⊕ Fin (n - a), where vertices in Fin a form a clique, vertices in Fin (n - a) induce the Turán graph T_{r-1}(n-a), and all cross-edges between Fin a and Fin (n - a) are present.
-/

/-- The graph join of the complete graph K_a and the Turan graph T_{r-1}(n-a) on vertices Fin a ⊕ Fin (n - a). -/
def join_complete_turan (n r a : ℕ) : SimpleGraph (Fin a ⊕ Fin (n - a)) := {
  Adj
    | Sum.inl u, Sum.inl v => u ≠ v
    | Sum.inr u, Sum.inr v => (SimpleGraph.turanGraph (n - a) (r - 1)).Adj u v
    | Sum.inl _, Sum.inr _ => True
    | Sum.inr _, Sum.inl _ => True
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact h.symm
    · trivial
    · trivial
    · exact (SimpleGraph.turanGraph (n - a) (r - 1)).adj_symm h⟩
  loopless := ⟨by
    rintro (u | u) h
    · exact h rfl
    · exact (SimpleGraph.turanGraph (n - a) (r - 1)).loopless.irrefl u h⟩
}
