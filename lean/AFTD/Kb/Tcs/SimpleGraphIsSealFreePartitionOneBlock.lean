import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsSealFreePartition

/-!
# simple_graph_is_seal_free_partition_one_block

Topic: graphs   Node: a935a606a79d

Provenance: helper lemma. step towards quadripartite_minimum_coloring_max_wild_number_eq

If G is a connected graph with edge colouring γ, then the one-block vertex map (everything ↦ 0) is a seal-free partition.
-/

/-- A connected graph always admits a seal-free partition into one block, so the definition is satisfiable. -/
theorem simple_graph_is_seal_free_partition_one_block {V α : Type*} (G : SimpleGraph V)
    (γ : G.edgeSet → α) (hG : G.Connected) :
    simple_graph_is_seal_free_partition G γ 1 (fun _ => 0) := by
  dsimp [simple_graph_is_seal_free_partition]
  refine ⟨fun i => ?_, fun e T hT_nonempty hT_ne_univ => ?_⟩
  · have hs : {v : V | (fun _ => (0 : Fin 1)) v = i} = (Set.univ : Set V) := by
      ext v
      simp [Subsingleton.elim ((fun _ => (0 : Fin 1)) v) i]
    rw [hs]
    exact (SimpleGraph.induceUnivIso G).connected_iff.mpr hG
  · obtain ⟨x, hx⟩ := hT_nonempty
    have hT_univ : T = Finset.univ := by
      ext y
      simp only [Finset.mem_univ, iff_true]
      have : y = x := Subsingleton.elim y x
      rwa [this]
    exact False.elim (hT_ne_univ hT_univ)
