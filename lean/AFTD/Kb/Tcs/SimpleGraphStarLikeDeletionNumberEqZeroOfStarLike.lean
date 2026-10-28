import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarLikeDeletionNumber
import AFTD.Kb.Tcs.SimpleGraphIsStarLike
import AFTD.Kb.Tcs.SimpleGraphLeafNeighborCount

/-!
# simple_graph_star_like_deletion_number_eq_zero_of_star_like

Topic: graphs   Node: f5ecea22d38c

Provenance: helper lemma. step towards dominating_average_star_like_vertex_stability

If a finite simple graph G is star-like, its star-like deletion number d_*(G) is zero.
-/

/-- The value of `G.degree v` does not depend on the chosen `Fintype` instance of the neighbour set. -/
private lemma simple_graph_star_like_deletion_number_eq_zero_of_star_like_deg_irrel {V : Type*} (G : SimpleGraph V) (v : V)
    (i₁ i₂ : Fintype ↑(G.neighborSet v)) :
    @SimpleGraph.degree V G v i₁ = @SimpleGraph.degree V G v i₂ := by
  show @Finset.card V (@Set.toFinset V (G.neighborSet v) i₁) = @Finset.card V (@Set.toFinset V (G.neighborSet v) i₂)
  have h : @Set.toFinset V (G.neighborSet v) i₁ = @Set.toFinset V (G.neighborSet v) i₂ :=
    Finset.coe_inj.mp (by rw [Set.coe_toFinset, Set.coe_toFinset])
  rw [h]

/-- If every vertex lies in `s`, the degree of a vertex in the induced subgraph on `s` equals its degree in `G`. -/
private lemma simple_graph_star_like_deletion_number_eq_zero_of_star_like_degree_induce_transfer {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Set V} [DecidablePred (· ∈ s)]
    (hs : ∀ v, v ∈ s) (u : ↥s)
    (i : Fintype ↑((SimpleGraph.induce s G).neighborSet u))
    (j : Fintype ↑(G.neighborSet (↑u : V))) :
    @SimpleGraph.degree _ (SimpleGraph.induce s G) u i = @SimpleGraph.degree _ G (↑u : V) j := by
  have h := SimpleGraph.degree_induce_of_neighborSet_subset (G := G) (s := s) (v := u) (fun x _ => hs x)
  exact (simple_graph_star_like_deletion_number_eq_zero_of_star_like_deg_irrel _ u i _).trans
    (h.trans (simple_graph_star_like_deletion_number_eq_zero_of_star_like_deg_irrel _ _ _ j))

/-- If every vertex lies in `s`, the number of leaf neighbours of a vertex is the same in the induced subgraph on `s` as in `G`. -/
private lemma simple_graph_star_like_deletion_number_eq_zero_of_star_like_leaf_count_induce {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Set V} [DecidablePred (· ∈ s)]
    (hs : ∀ v, v ∈ s) (w : ↥s) :
    simple_graph_leaf_neighbor_count (SimpleGraph.induce s G) w
      = simple_graph_leaf_neighbor_count G (↑w : V) := by
  simp only [simple_graph_leaf_neighbor_count]
  refine Finset.card_bij (fun u _ => (↑u : V)) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset] at hu ⊢
      exact SimpleGraph.induce_adj.mp hu.1
    · exact (simple_graph_star_like_deletion_number_eq_zero_of_star_like_degree_induce_transfer (G := G) hs u _ _).symm.trans hu.2
  · intro u₁ _ u₂ _ h
    exact Subtype.ext h
  · intro b hb
    rw [Finset.mem_filter] at hb
    refine ⟨⟨b, hs b⟩, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.mem_neighborFinset]
      rw [SimpleGraph.mem_neighborFinset] at hb
      exact SimpleGraph.induce_adj.mpr hb.1
    · exact (simple_graph_star_like_deletion_number_eq_zero_of_star_like_degree_induce_transfer (G := G) hs ⟨b, hs b⟩ _ _).trans hb.2

/-- Star-likeness passes to the induced subgraph on any vertex set containing all vertices. -/
private lemma simple_graph_star_like_deletion_number_eq_zero_of_star_like_star_like_induce {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {s : Set V} [DecidablePred (· ∈ s)]
    (hs : ∀ v, v ∈ s) (hstar : simple_graph_is_star_like G) :
    simple_graph_is_star_like (SimpleGraph.induce s G) := by
  intro w
  have hw := hstar (↑w : V)
  rw [simple_graph_star_like_deletion_number_eq_zero_of_star_like_degree_induce_transfer (G := G) hs w _ _,
    simple_graph_star_like_deletion_number_eq_zero_of_star_like_leaf_count_induce (G := G) hs w]
  exact hw

/-- If G is star-like, then its star-like deletion number d_*(G) is zero. -/
theorem simple_graph_star_like_deletion_number_eq_zero_of_star_like {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (hstar : simple_graph_is_star_like G) : simple_graph_star_like_deletion_number G = 0 := by
  unfold simple_graph_star_like_deletion_number
  refine Nat.sInf_eq_zero.mpr (Or.inl ?_)
  refine ⟨∅, ?_, rfl⟩
  exact simple_graph_star_like_deletion_number_eq_zero_of_star_like_star_like_induce (G := G)
    (s := ((↑(∅ : Finset V)) : Set V)ᶜ) (fun v => by simp) hstar
