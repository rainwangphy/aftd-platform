import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MovingTargetStrategySuccessful
import AFTD.Kb.GameTheoryEconomics.GridGraph
import AFTD.Kb.GameTheoryEconomics.SweepQuery
import AFTD.Kb.GameTheoryEconomics.SweepQueryCard
import AFTD.Kb.GameTheoryEconomics.MovingTargetStrategy
import AFTD.Kb.Physics.InstDecidableRelPathGraph
import AFTD.Kb.GameTheoryEconomics.ClosedNeighborhood

/-!
# moving_target_grid_accuracy_le_min

Topic: combinatorial_games   Node: 9bc8d687051a

Provenance: formalization of a published result. Source: arXiv:2611.01281 (Two-Dimensional Search for a Moving Target on Rectangular and Cylindrical Grids), Theorem 5.1, in the model of its Definitions 2.1-2.2 (knowledge base: MovingTargetStrategy, moving_target_strategy_successful, grid_graph). s*(M,N) ≤ s is stated as the existence of a successful strategy of accuracy s. Proof follows the paper: the diagonal sweep of queries T_{r,j} (sweep_query) with candidate bound after each negative answer, transposed through the swap of the grid for the bound M+1, and the 1×1 grid by stopping at once.

For all M, N ≥ 1, on the M × N rectangular grid (vertices Fin M × Fin N, adjacent when they differ by one in exactly one coordinate) there is a finite deterministic adaptive search strategy for a moving target with accuracy min(M+1, N+1): starting from the candidate set of all vertices, in each round the target may stay or move to a neighbor (the candidate set C becomes the closed neighborhood of the previous set D), the searcher queries a set Q and the new candidate set is C ∩ Q or C \ Q according to the answer, and on every feasible branch (nonempty new candidate set) the strategy stops with a candidate set of at most min(M+1, N+1) vertices. Equivalently, the optimal localization accuracy satisfies s*(M,N) ≤ min(M+1, N+1).
-/

/-- The diagonal sweep of arXiv:2611.01281 Sec. 5 from query (r, j) on. -/
def grid_sweep_strategy (M N : ℕ) (r j : ℕ) : MovingTargetStrategy (Fin M × Fin N) :=
  if r + 1 < M then
    if j < N then .query (sweep_query M N r j) (grid_sweep_strategy M N r (j + 1)) .stop
    else grid_sweep_strategy M N (r + 1) 0
  else .stop
termination_by (M - r, N - j)

/-- The region still possible before sweep query (r, j). -/
def grid_sweep_region (M N : ℕ) (r j : ℕ) : Finset (Fin M × Fin N) :=
  Finset.univ.filter fun p => (p.1.val = r + 1 ∧ j ≤ p.2.val) ∨ r + 2 ≤ p.1.val

theorem grid_graph_adj_iff (M N : ℕ) (u p : Fin M × Fin N) :
    (grid_graph M N).Adj u p ↔
      ((u.1.val + 1 = p.1.val ∨ p.1.val + 1 = u.1.val) ∧ u.2.val = p.2.val) ∨
      ((u.2.val + 1 = p.2.val ∨ p.2.val + 1 = u.2.val) ∧ u.1.val = p.1.val) := by
  simp [grid_graph, SimpleGraph.boxProd_adj, SimpleGraph.pathGraph_adj, Fin.ext_iff]

theorem mem_closed_neighborhood_iff {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) :
    v ∈ closed_neighborhood G A ↔ ∃ u ∈ A, u = v ∨ G.Adj u v := by
  simp [closed_neighborhood]

theorem grid_sweep_strategy_successful (M N : ℕ) [DecidableRel (grid_graph M N).Adj] (r j : ℕ)
    (hj : j ≤ N) (D : Finset (Fin M × Fin N)) (hD : D ⊆ grid_sweep_region M N r j) :
    moving_target_strategy_successful (grid_graph M N) (N + 1) (grid_sweep_strategy M N r j) D := by
  rw [grid_sweep_strategy]
  split_ifs with hr hjN
  · simp only [moving_target_strategy_successful]
    constructor
    · intro _
      apply grid_sweep_strategy_successful M N r (j + 1) (by omega)
      intro p hp
      rw [Finset.mem_sdiff, mem_closed_neighborhood_iff] at hp
      obtain ⟨⟨u, hu, hup⟩, hpT⟩ := hp
      have hu' := hD hu
      simp only [grid_sweep_region, sweep_query, Finset.mem_filter, Finset.mem_univ, true_and] at hu' hpT ⊢
      rcases hup with rfl | hadj
      · omega
      · rw [grid_graph_adj_iff] at hadj
        have := p.2.isLt
        omega
    · intro _
      calc (closed_neighborhood (grid_graph M N) D ∩ sweep_query M N r j).card
          ≤ (sweep_query M N r j).card := Finset.card_le_card Finset.inter_subset_right
        _ = N + 1 := sweep_query_card M N r j hr hjN
  · apply grid_sweep_strategy_successful M N (r + 1) 0 (by omega)
    intro p hp
    have hp' := hD hp
    simp only [grid_sweep_region, Finset.mem_filter, Finset.mem_univ, true_and] at hp' ⊢
    have := p.2.isLt
    omega
  · simp only [moving_target_strategy_successful]
    have : D = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      have hp' := hD hp
      simp only [grid_sweep_region, Finset.mem_filter, Finset.mem_univ, true_and] at hp'
      have := p.1.isLt
      omega
    simp [this]
termination_by (M - r, N - j)

theorem grid_sweep_strategy_univ_successful (M N : ℕ) [DecidableRel (grid_graph M N).Adj]
    (hM : 2 ≤ M) (hN : 1 ≤ N) :
    moving_target_strategy_successful (grid_graph M N) (N + 1) (grid_sweep_strategy M N 0 0)
      Finset.univ := by
  rw [grid_sweep_strategy, if_pos (by omega), if_pos (by omega)]
  simp only [moving_target_strategy_successful]
  constructor
  · intro _
    apply grid_sweep_strategy_successful M N 0 1 (by omega)
    intro p hp
    rw [Finset.mem_sdiff] at hp
    obtain ⟨_, hpT⟩ := hp
    simp only [grid_sweep_region, sweep_query, Finset.mem_filter, Finset.mem_univ, true_and] at hpT ⊢
    omega
  · intro _
    calc (closed_neighborhood (grid_graph M N) Finset.univ ∩ sweep_query M N 0 0).card
        ≤ (sweep_query M N 0 0).card := Finset.card_le_card Finset.inter_subset_right
      _ = N + 1 := sweep_query_card M N 0 0 (by omega) (by omega)

/-- Transport of a search strategy along a bijection of the vertex sets. -/
def moving_target_strategy_map_equiv {V W : Type*} (e : V ≃ W) :
    MovingTargetStrategy V → MovingTargetStrategy W
  | .stop => .stop
  | .query Q f t => .query (Q.map e.toEmbedding) (moving_target_strategy_map_equiv e f)
      (moving_target_strategy_map_equiv e t)

theorem moving_target_strategy_successful_map_equiv {V W : Type*} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (G : SimpleGraph V) [DecidableRel G.Adj]
    (G' : SimpleGraph W) [DecidableRel G'.Adj] (e : V ≃ W)
    (he : ∀ a b, G'.Adj (e a) (e b) ↔ G.Adj a b) (s : ℕ) (S : MovingTargetStrategy V) :
    ∀ D : Finset V, moving_target_strategy_successful G s S D →
      moving_target_strategy_successful G' s (moving_target_strategy_map_equiv e S)
        (D.map e.toEmbedding) := by
  have hΓ : ∀ D : Finset V, closed_neighborhood G' (D.map e.toEmbedding) =
      (closed_neighborhood G D).map e.toEmbedding := by
    intro D
    ext q
    obtain ⟨p, rfl⟩ := e.surjective q
    rw [mem_closed_neighborhood_iff, show (e p ∈ (closed_neighborhood G D).map e.toEmbedding) ↔
        p ∈ closed_neighborhood G D from Finset.mem_map' e.toEmbedding, mem_closed_neighborhood_iff]
    constructor
    · rintro ⟨u', hu', h⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hu'
      refine ⟨u, hu, ?_⟩
      simpa [he] using h
    · rintro ⟨u, hu, h⟩
      refine ⟨e u, Finset.mem_map_of_mem _ hu, ?_⟩
      simpa [he] using h
  induction S with
  | stop =>
    intro D hD
    simpa [moving_target_strategy_successful, moving_target_strategy_map_equiv] using hD
  | query Q f t ihf iht =>
    intro D hD
    simp only [moving_target_strategy_successful] at hD
    simp only [moving_target_strategy_map_equiv, moving_target_strategy_successful]
    rw [hΓ, ← Finset.map_sdiff, ← Finset.map_inter]
    refine ⟨fun h => ihf _ (hD.1 ?_), fun h => iht _ (hD.2 ?_)⟩
    · simpa using h
    · simpa using h

open scoped Classical in
theorem moving_target_grid_accuracy_le_min (M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N) :
    ∃ S : MovingTargetStrategy (Fin M × Fin N),
      moving_target_strategy_successful (grid_graph M N) (min (M + 1) (N + 1)) S Finset.univ := by
  by_cases hMN : M ≤ N
  · rw [min_eq_left (by omega)]
    by_cases hN2 : 2 ≤ N
    · have h := grid_sweep_strategy_univ_successful N M hN2 hM
      have h2 := moving_target_strategy_successful_map_equiv (grid_graph N M) (grid_graph M N)
        (Equiv.prodComm (Fin N) (Fin M)) (fun a b => by
          simp only [Equiv.prodComm_apply, grid_graph_adj_iff, Prod.fst_swap, Prod.snd_swap]
          tauto) _ _ _ h
      rw [Finset.map_univ_equiv] at h2
      exact ⟨_, h2⟩
    · refine ⟨.stop, ?_⟩
      simp only [moving_target_strategy_successful, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin]
      have : M = 1 := by omega
      have : N = 1 := by omega
      subst_vars
      norm_num
  · rw [min_eq_right (by omega)]
    exact ⟨_, grid_sweep_strategy_univ_successful M N (by omega) hN⟩
