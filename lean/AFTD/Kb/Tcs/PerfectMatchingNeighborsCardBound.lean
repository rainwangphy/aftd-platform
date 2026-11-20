import AFTD.Prelude

/-!
# perfect_matching_neighbors_card_bound

Topic: graphs   Node: 9fa9217a7491

Provenance: helper lemma. Elementary perfect-matching cardinal bound for the OP-1957 codegree-three analysis.

In a graph with a perfect matching, a set whose neighbors all lie in C has size at most |C|.
-/

theorem perfect_matching_neighbors_card_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (P : G.Subgraph) (hP : P.IsPerfectMatching) (T C : Finset V)
    (hcover : ∀ t ∈ T, ∀ v, G.Adj t v → v ∈ C) : T.card ≤ C.card := by
  classical
  have hp := SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  let f : V → V := fun x => Classical.choose (hp x)
  have hf : ∀ a, P.Adj a (f a) := fun a => (Classical.choose_spec (hp a)).1
  apply Finset.card_le_card_of_injOn f
  · intro a ha
    exact hcover a ha (f a) (P.adj_sub (hf a))
  · intro a ha b hb hab
    have h1 : P.Adj (f a) a := (hf a).symm
    have h2 : P.Adj (f a) b := by rw [hab]; exact (hf b).symm
    exact (hp (f a)).unique h1 h2
