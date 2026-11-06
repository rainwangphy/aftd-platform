import AFTD.Prelude

/-!
# apex_graph_fin

Topic: communication   Node: 35fc8c81a00a

Provenance: helper lemma. step towards oneway_connected_components_reduction_from_connectivity

Given a graph H on Fin n and a subset S of Fin n, the apex graph on Fin (n + 1) retains the edges of H on Fin n and connects the apex vertex n to each vertex in S.
-/

/-- Given a graph H on Fin n and a subset S ⊆ Fin n, apex_graph_fin n H S is the simple graph on Fin (n + 1) with base graph H and star edges from apex vertex n to S. -/
def apex_graph_fin (n : ℕ) (H : SimpleGraph (Fin n)) (S : Finset (Fin n)) : SimpleGraph (Fin (n + 1)) := {
  Adj := fun u v =>
    if hu : u.val < n then
      if hv : v.val < n then
        H.Adj ⟨u.val, hu⟩ ⟨v.val, hv⟩
      else
        ⟨u.val, hu⟩ ∈ S
    else
      if hv : v.val < n then
        ⟨v.val, hv⟩ ∈ S
      else
        False
  symm := ⟨by
    intro u v h
    split_ifs at h with h1 h2 <;> split_ifs with h3 h4 <;>
      first | contradiction | exact h | exact H.adj_symm h⟩
  loopless := ⟨by
    intro u h
    split_ifs at h with h1 h2 <;> first | contradiction | exact H.irrefl h⟩
}
