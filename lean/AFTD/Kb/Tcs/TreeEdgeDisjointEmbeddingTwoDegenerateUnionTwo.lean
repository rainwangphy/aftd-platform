import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsDegenerate

/-!
# tree_edge_disjoint_embedding_two_degenerate_union_two

Topic: graphs   Node: e467a5c6ffd3

Provenance: helper lemma. arXiv:2611.04674, Lemma 2.1

For n = 2, any tree S on Fin 1 can be embedded into Fin 2 edge-disjointly from a spanning tree T on Fin 2 such that the union graph T ⊔ S.map φ is 2-degenerate.
-/

/-- Base case n = 2 of Lemma 2.1: any tree on 1 vertex can be embedded into K_2 disjointly from a spanning tree on 2 vertices with 2-degenerate union. -/
theorem tree_edge_disjoint_embedding_two_degenerate_union_two
    (T : SimpleGraph (Fin 2)) (hT : T.IsTree)
    (S : SimpleGraph (Fin 1)) (hS : S.IsTree) :
    ∃ φ : Fin 1 ↪ Fin 2,
      Disjoint T (S.map φ) ∧ simple_graph_is_degenerate (T ⊔ S.map φ) 2 := by
  let φ : Fin 1 ↪ Fin 2 := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩
  have hS_map : S.map φ = ⊥ := by
    ext u v
    simp only [SimpleGraph.map_adj, SimpleGraph.bot_adj, iff_false]
    rintro ⟨x, y, hAdj, -⟩
    have : x = y := Subsingleton.elim x y
    subst this
    exact S.irrefl hAdj
  refine ⟨φ, ?_, ?_⟩
  · rw [hS_map]
    exact disjoint_bot_right
  · rw [hS_map, sup_bot_eq]
    intro s hs
    obtain ⟨v, hv⟩ := hs
    refine ⟨v, hv, ?_⟩
    have h1 : (s ∩ T.neighborSet v).encard ≤ (Set.univ : Set (Fin 2)).encard :=
      Set.encard_le_encard (Set.subset_univ _)
    have h2 : (Set.univ : Set (Fin 2)).encard = 2 := by simp
    rwa [h2] at h1
