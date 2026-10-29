import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCardCommonNeighborsAddTwoLeDegree
import AFTD.Kb.Tcs.IsAmplyRegular

/-!
# amply_regular_lambda_add_two_le_degree_of_three_le_diam

Topic: graphs   Node: 7712a95d9126

Provenance: helper lemma. step towards amply_regular_diameter_bound_conjecture

An amply regular graph with parameters (k, ℓ, μ) whose diameter is at least 3 satisfies ℓ + 2 ≤ k. (Equivalently: if k ≤ ℓ + 1 then the diameter is at most 2.)
-/

/-- Necessary condition for the hard regime: a diameter of at least 3 forces k ≥ ℓ+2, so the bound 2k/(ℓ+2) is at least 2 there and the conjecture cannot be settled by the diam ≤ 2 argument. -/
theorem amply_regular_lambda_add_two_le_degree_of_three_le_diam {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k ℓ μ : ℕ} (hG : IsAmplyRegular G k ℓ μ) (h3 : 3 ≤ G.diam) :
    ℓ + 2 ≤ k := by
  classical
  have hpos : G.diam ≠ 0 := by omega
  have : Nonempty V := (SimpleGraph.nontrivial_of_diam_ne_zero hpos).to_nonempty
  obtain ⟨x, y, hxy⟩ := SimpleGraph.exists_dist_eq_diam (G := G)
  have hd : 3 ≤ G.dist x y := by omega
  have hreach : G.Reachable x y := by
    by_contra hc
    rw [SimpleGraph.dist_eq_zero_of_not_reachable hc] at hd
    omega
  obtain ⟨p, hp⟩ := hreach.exists_walk_length_eq_dist
  have hlen : 3 ≤ p.length := by omega
  have h1 : G.Adj x (p.getVert 1) := by
    have := p.adj_getVert_succ (i := 0) (by omega); simpa using this
  have h2 : G.Adj (p.getVert 1) (p.getVert 2) := by
    have := p.adj_getVert_succ (i := 1) (by omega); simpa using this
  have hnadj : ¬ G.Adj x (p.getVert 2) := by
    intro hadj
    have hle := SimpleGraph.dist_le (G := G) (SimpleGraph.Walk.cons hadj (p.drop 2))
    rw [SimpleGraph.Walk.length_cons] at hle
    have h2' : (p.drop 2).length = p.length - 2 := by simp
    omega
  have key : ∀ {a : V}, a = p.getVert 2 → G.dist a y ≤ (p.drop 2).length := by
    intro a ha
    rw [ha]
    exact SimpleGraph.dist_le (p.drop 2)
  have hbx : x ≠ p.getVert 2 := by
    intro h
    have hle := key h
    have h2' : (p.drop 2).length = p.length - 2 := by simp
    omega
  have hcount := simple_graph_card_commonNeighbors_add_two_le_degree G hG.regular hbx h1 h2.symm hnadj
  have hEll : Fintype.card (G.commonNeighbors x (p.getVert 1)) = ℓ := hG.adj_commonNeighbors h1
  omega
