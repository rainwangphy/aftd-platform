import AFTD.Prelude
import AFTD.Kb.Tcs.IsThresholdSequence
import AFTD.Kb.Tcs.LooplessDigraphCount

/-!
# threshold_loopless_digraph_ge_one

Topic: graphs   Node: 40199c0bf833

Provenance: helper lemma. arXiv:2611.02191 Sec. 1.1; Csikvari and Imolay (2020)

For every natural number n and every threshold degree sequence d on n vertices, there exists at least one loopless digraph with in-degree and out-degree equal to d, so D(d) ≥ 1.
-/

/-- Every threshold degree sequence has at least one loopless digraph realization, namely its symmetric realization. -/
theorem threshold_loopless_digraph_ge_one (n : ℕ) (d : Fin n → ℕ) (h : is_threshold_sequence d) : 1 ≤ loopless_digraph_count d := by
  classical
  rcases h with ⟨G, -, hdeg⟩
  unfold loopless_digraph_count
  rw [Nat.succ_le_iff]
  apply Finset.card_pos.2
  refine ⟨⟨G.Adj⟩, ?_⟩
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro v
    exact G.irrefl
  · intro v
    have h1 : (Finset.univ.filter (fun w => G.Adj v w)) = G.neighborFinset v := by
      ext w; simp
    rw [h1, SimpleGraph.card_neighborFinset_eq_degree, hdeg v]
  · intro v
    have h1 : (Finset.univ.filter (fun u => G.Adj u v)) = G.neighborFinset v := by
      ext u; simp [G.adj_comm]
    rw [h1, SimpleGraph.card_neighborFinset_eq_degree, hdeg v]
