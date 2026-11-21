import AFTD.Prelude

/-!
# perfect_matching_of_adjacency_involution

Topic: graphs   Node: d497304690e6

Provenance: helper lemma. OP-1957: explicit matching witness.

A simple graph has a perfect matching if it has an involution that sends every vertex to an adjacent vertex.
-/

theorem perfect_matching_of_adjacency_involution {V : Type*} (G : SimpleGraph V) (f : V → V)
    (hinv : Function.Involutive f) (hadj : ∀ x, G.Adj x (f x)) :
    ∃ P : G.Subgraph, P.IsPerfectMatching := by
  classical
  let P : G.Subgraph := ⟨Set.univ, fun x y => y = f x,
    by intro x y h; subst y; exact hadj x,
    by intro x y h; exact Set.mem_univ x,
    by
      constructor
      intro x y h
      subst y
      exact (hinv x).symm⟩
  refine ⟨P, ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro x
  exact ⟨f x, rfl, fun y h => h⟩
