import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphThreeVertexConnected

/-!
# simple_graph_three_vertex_connected_three_le_degree

Topic: graphs   Node: 0c0fc4553d62

Provenance: helper lemma. Sanity lemma for simple_graph_three_vertex_connected (OP-541)

Every vertex of a 3-vertex-connected graph has degree at least 3 (sanity check of simple_graph_three_vertex_connected).
-/

theorem simple_graph_three_vertex_connected_three_le_degree_helper {V : Type*}
    (G : SimpleGraph V) (u w : V) (hne : u ≠ w)
    (h_no_adj : ∀ x, ¬ G.Adj u x) : ¬ G.Reachable u w := by
  intro ⟨p⟩
  cases p with
  | nil => exact hne rfl
  | cons hadj p' => exact h_no_adj _ hadj

theorem simple_graph_three_vertex_connected_three_le_degree {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (h : simple_graph_three_vertex_connected G) (v : Fin n) :
    3 ≤ G.degree v := by
  by_contra! hdeg
  have h4 : 4 ≤ n := h.1
  have hnot : v ∉ G.neighborFinset v := G.notMem_neighborFinset_self v
  have hcard : (insert v (G.neighborFinset v)).card ≤ 3 := by
    rw [Finset.card_insert_of_notMem hnot, G.card_neighborFinset_eq_degree]
    omega
  have hcard_lt : (insert v (G.neighborFinset v)).card < Fintype.card (Fin n) := by
    rw [Fintype.card_fin]
    omega
  obtain ⟨w, hw⟩ : ∃ w : Fin n, w ∉ insert v (G.neighborFinset v) := by
    by_contra! hc
    have hs := Finset.eq_univ_of_forall hc
    rw [hs, Finset.card_univ] at hcard_lt
    exact lt_irrefl _ hcard_lt
  rw [Finset.mem_insert, not_or] at hw
  have hw_not_mem : w ∉ G.neighborFinset v := hw.2
  have hw_ne_v : w ≠ v := hw.1
  let X := G.neighborFinset v
  have hX_card : X.card ≤ 2 := by
    rw [G.card_neighborFinset_eq_degree]
    omega
  have hconn := h.2 X hX_card
  have hv_s : v ∈ (↑X : Set (Fin n))ᶜ := hnot
  have hw_s : w ∈ (↑X : Set (Fin n))ᶜ := hw_not_mem
  let u_v : ↥(↑X : Set (Fin n))ᶜ := ⟨v, hv_s⟩
  let u_w : ↥(↑X : Set (Fin n))ᶜ := ⟨w, hw_s⟩
  have hne : u_v ≠ u_w := by
    intro heq
    have : u_v.1 = u_w.1 := congr_arg Subtype.val heq
    exact hw_ne_v this.symm
  have h_no_adj : ∀ x : ↥(↑X : Set (Fin n))ᶜ, ¬ (SimpleGraph.induce (↑X)ᶜ G).Adj u_v x := by
    intro x hadj
    rw [SimpleGraph.induce_adj] at hadj
    have hx_adj : x.1 ∈ G.neighborFinset v := (G.mem_neighborFinset v x.1).2 hadj
    exact x.2 hx_adj
  have h_not_reach := simple_graph_three_vertex_connected_three_le_degree_helper
    (SimpleGraph.induce (↑X)ᶜ G) u_v u_w hne h_no_adj
  exact h_not_reach (hconn.preconnected u_v u_w)
