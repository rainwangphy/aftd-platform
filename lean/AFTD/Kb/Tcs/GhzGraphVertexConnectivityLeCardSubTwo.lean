import AFTD.Prelude
import AFTD.Kb.Tcs.GhzVertexConnectivityLeCardOfCut
import AFTD.Kb.Tcs.GhzGraphVertexConnectivity

/-!
# ghz_graph_vertex_connectivity_le_card_sub_two

Topic: graphs   Node: 1844dbcf788e

Provenance: helper lemma. step towards radius_independence_connectivity_hamiltonian_interpolation

If G is not the complete graph, there exist two distinct non-adjacent vertices u and v. Setting T = (V \ {u, v}) yields an induced subgraph on {u, v} which is disconnected, so the vertex connectivity is at most |T| = |V| - 2.
-/

/-- Every finite simple graph that is not the complete graph has vertex connectivity at most |V| - 2. -/
theorem ghz_graph_vertex_connectivity_le_card_sub_two {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (hne : G ≠ ⊤) : ghz_graph_vertex_connectivity G ≤ Fintype.card V - 2 := by
  classical
  -- A graph which is not complete has two distinct non-adjacent vertices.
  obtain ⟨u, w, huw, hadj⟩ : ∃ a b : V, a ≠ b ∧ ¬ G.Adj a b := by
    by_contra hc
    simp only [not_exists, not_and] at hc
    refine hne (SimpleGraph.eq_top_iff_forall_ne_adj.mpr fun a b hab => ?_)
    by_contra hnab
    exact hc a b hab hnab
  -- The induced subgraph on `{u, w}` has no edge at all.
  have hno : ∀ (x y : ({u, w} : Set V)),
      ¬ (SimpleGraph.induce ({u, w} : Set V) G).Adj x y := by
    intro x y hxy
    simp only [SimpleGraph.induce_adj] at hxy
    have hx : (x : V) = u ∨ (x : V) = w := by
      have h' := x.2; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h'; exact h'
    have hy : (y : V) = u ∨ (y : V) = w := by
      have h' := y.2; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h'; exact h'
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · rw [hx, hy] at hxy; exact G.irrefl hxy
    · rw [hx, hy] at hxy; exact hadj hxy
    · rw [hx, hy] at hxy; exact hadj hxy.symm
    · rw [hx, hy] at hxy; exact G.irrefl hxy
  -- Take the cut `T = V \ {u, w}`; its complement induces a graph on `{u, w}`.
  refine le_trans (ghz_vertex_connectivity_le_card_of_cut G
    (Finset.univ \ ({u, w} : Finset V)) ?_) ?_
  · have hcoe : (((Finset.univ \ ({u, w} : Finset V)) : Finset V) : Set V)ᶜ
        = ({u, w} : Set V) := by
      simp only [Finset.coe_sdiff, Finset.coe_univ, Finset.coe_insert, Finset.coe_singleton]
      ext x; simp; tauto
    rw [hcoe]
    intro hp
    have hreach : (SimpleGraph.induce ({u, w} : Set V) G).Reachable
        ⟨u, by simp⟩ ⟨w, by simp⟩ := hp _ _
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    -- With no adjacencies, a reachability relation forces the endpoints to agree.
    have heq : (⟨w, by simp⟩ : ({u, w} : Set V)) = ⟨u, by simp⟩ :=
      (Relation.reflTransGen_iff_eq (fun b => hno _ b)).mp hreach
    exact huw (congrArg Subtype.val heq).symm
  · rw [Finset.card_univ_sdiff, Finset.card_pair huw]
