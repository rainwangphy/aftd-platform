import AFTD.Prelude
import AFTD.Kb.Tcs.IsClawFreeTripleNeighbors
import AFTD.Kb.Tcs.NetGraph
import AFTD.Kb.Tcs.IsClawFree
import AFTD.Kb.Tcs.IsPkFree
import AFTD.Kb.Tcs.IsPkFreeOfCardLt
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# not_p7_claw_free_dominating_pair_of_no_hole

Topic: graphs   Node: 146e0aeef398

Provenance: original. Related work: refutes `p7_claw_free_dominating_pair_of_no_hole`

The statement `p7_claw_free_dominating_pair_of_no_hole` is false: The statement is FALSE. A concrete counterexample is the net graph (a central triangle with a pendant vertex attached to each vertex of the triangle) on 6 vertices:
- Vertex set: {0, 1, 2, 3, 4, 5}.
- Edges: (0, 3), (0, 4), (0, 5), (1, 4), (2, 5), (4, 5).

Verification of hypotheses:
1. `Connected`: The graph is connected (triangle {0, 4, 5} with leaves 1, 2, 3 attached).
2. `IsPkFree G 7`: The graph has only 6 vertices, so |V| < 7 implies it contains no induced P_7.
3. `IsClawFree G`: The only vertices of degree ≥ 3 are 0, 4, and 5. In each case, two of their three neighbors are mutually adjacent (forming the central triangle), so no vertex has an independent set of 3 neighbors. Thus G is claw-free.
4. `∀ m ≥ 6, IsEmpty (cycleGraph m ↪g G)`: The only cycle in G has length 3; there is no cycle of length ≥ 6 (for m > 6, |V| = 6 < m; for m = 6, degrees are 3, 3, 3, 1, 1, 1, so no 2-regular subgraph exists).

Failure of conclusion:
In G, every vertex has closed neighborhood of size at most 4 (the vertices 0, 4, 5 have closed neighborhoods of size 4; vertices 1, 2, 3 have closed neighborhoods of size 2).
Every pair {u, v} leaves at least one leaf vertex uncovered:
- {0, 4} does not dominate 2.
- {0, 5} does not dominate 1.
- {4, 5} does not dominate 3.
- Any pair involving a leaf dominates strictly fewer vertices.
Thus no dominating pair exists (the domination number of the net graph is 3).
-/

lemma not_p7_net_adj_iff.{u} (a b : Fin 6) :
    net_graph.{u}.Adj ⟨a⟩ ⟨b⟩ ↔ (a.val, b.val) ∈ ([(0, 3), (3, 0), (0, 4), (4, 0), (0, 5), (5, 0),
      (1, 4), (4, 1), (2, 5), (5, 2), (4, 5), (5, 4)] : List (ℕ × ℕ)) := by
  simp only [net_graph, SimpleGraph.fromRel_adj, ne_eq, ULift.up.injEq]
  fin_cases a <;> fin_cases b <;> decide

lemma not_p7_net_reachable.{u} (x : ULift.{u} (Fin 6)) : net_graph.Reachable ⟨0⟩ x := by
  obtain ⟨x⟩ := x
  have a : ∀ p q : Fin 6, net_graph.{u}.Adj ⟨p⟩ ⟨q⟩ → net_graph.{u}.Reachable ⟨p⟩ ⟨q⟩ :=
    fun p q h => h.reachable
  fin_cases x
  · rfl
  · exact (a 0 4 (by rw [not_p7_net_adj_iff]; decide)).trans (a 4 1 (by rw [not_p7_net_adj_iff]; decide))
  · exact (a 0 5 (by rw [not_p7_net_adj_iff]; decide)).trans (a 5 2 (by rw [not_p7_net_adj_iff]; decide))
  · exact a 0 3 (by rw [not_p7_net_adj_iff]; decide)
  · exact a 0 4 (by rw [not_p7_net_adj_iff]; decide)
  · exact a 0 5 (by rw [not_p7_net_adj_iff]; decide)

theorem not_p7_claw_free_dominating_pair_of_no_hole : ¬ (∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    (hconn : G.Connected) (hp : IsPkFree G 7) (hclaw : IsClawFree G)
    (hno_hole : ∀ m ≥ 6, IsEmpty (SimpleGraph.cycleGraph m ↪g G)), ∃ u v : V, ∀ w : V, w = u ∨ w = v ∨ G.Adj u w ∨ G.Adj v w) := by
  intro H
  have hconn : net_graph.{u_1}.Connected := by
    have : Nonempty (ULift.{u_1} (Fin 6)) := ⟨⟨0⟩⟩
    exact SimpleGraph.Connected.mk
      (fun x y => (not_p7_net_reachable x).symm.trans (not_p7_net_reachable y))
  have hp : IsPkFree net_graph.{u_1} 7 := is_pk_free_of_card_lt _ 7 (by simp)
  have hclaw : IsClawFree net_graph.{u_1} := by
    rintro ⟨f⟩
    have key : ∀ v a b c : Fin 6,
        net_graph.{u_1}.Adj ⟨v⟩ ⟨a⟩ → net_graph.{u_1}.Adj ⟨v⟩ ⟨b⟩ → net_graph.{u_1}.Adj ⟨v⟩ ⟨c⟩ →
        a ≠ b → a ≠ c → b ≠ c →
        net_graph.{u_1}.Adj ⟨a⟩ ⟨b⟩ ∨ net_graph.{u_1}.Adj ⟨a⟩ ⟨c⟩ ∨ net_graph.{u_1}.Adj ⟨b⟩ ⟨c⟩ := by
      simp only [not_p7_net_adj_iff]
      set_option synthInstance.maxSize 8192 in decide
    have hadj : ∀ i : Fin 3, net_graph.{u_1}.Adj (f (Sum.inl 0)) (f (Sum.inr i)) := fun i =>
      f.map_rel_iff.mpr (by simp)
    have hnadj : ∀ i j : Fin 3, ¬ net_graph.{u_1}.Adj (f (Sum.inr i)) (f (Sum.inr j)) := fun i j h =>
      by have := f.map_rel_iff.mp h; simp at this
    have hne : ∀ i j : Fin 3, i ≠ j → (f (Sum.inr i)).down ≠ (f (Sum.inr j)).down := by
      intro i j hij h
      exact hij (Sum.inr_injective (f.injective (ULift.ext _ _ h)))
    have := key (f (Sum.inl 0)).down (f (Sum.inr 0)).down (f (Sum.inr 1)).down (f (Sum.inr 2)).down
      (hadj 0) (hadj 1) (hadj 2) (hne 0 1 (by decide)) (hne 0 2 (by decide)) (hne 1 2 (by decide))
    rcases this with h | h | h
    · exact hnadj 0 1 h
    · exact hnadj 0 2 h
    · exact hnadj 1 2 h
  have hhole : ∀ m ≥ 6, IsEmpty (SimpleGraph.cycleGraph m ↪g net_graph.{u_1}) := by
    intro m hm
    refine ⟨fun f => ?_⟩
    have hcard := Fintype.card_le_of_injective f f.injective
    simp only [Fintype.card_fin, Fintype.card_ulift] at hcard
    obtain rfl : m = 6 := by omega
    have hinj : Function.Injective (fun i => (f i).down) := fun i j h =>
      f.injective (ULift.ext _ _ h)
    have hsurj := (Finite.injective_iff_surjective).mp hinj
    obtain ⟨i, hi⟩ := hsurj 1
    have h1 : (SimpleGraph.cycleGraph 6).Adj i (i + 1) := by
      rw [SimpleGraph.cycleGraph_adj]; right; simp
    have h2 : (SimpleGraph.cycleGraph 6).Adj i (i - 1) := by
      rw [SimpleGraph.cycleGraph_adj]; left; simp
    have e1 := f.map_rel_iff.mpr h1
    have e2 := f.map_rel_iff.mpr h2
    have k1 : ∀ y : Fin 6, net_graph.{u_1}.Adj ⟨1⟩ ⟨y⟩ → y = 4 := by
      simp only [not_p7_net_adj_iff]; decide
    have hfi : f i = ⟨1⟩ := ULift.ext _ _ hi
    rw [hfi] at e1 e2
    have q1 := k1 (f (i + 1)).down e1
    have q2 := k1 (f (i - 1)).down e2
    have : i + 1 = i - 1 := hinj (q1.trans q2.symm)
    have hne : ∀ j : Fin 6, j + 1 ≠ j - 1 := by decide
    exact hne i this
  obtain ⟨⟨u⟩, ⟨v⟩, h⟩ := H net_graph.{u_1} hconn hp hclaw hhole
  have key : ∀ u v : Fin 6, ∃ w : Fin 6, ¬ (w = u ∨ w = v ∨ net_graph.{u_1}.Adj ⟨u⟩ ⟨w⟩ ∨
      net_graph.{u_1}.Adj ⟨v⟩ ⟨w⟩) := by
    simp only [not_p7_net_adj_iff]; decide
  obtain ⟨w, hw⟩ := key u v
  rcases h ⟨w⟩ with h | h | h | h
  · exact hw (Or.inl (by simpa using h))
  · exact hw (Or.inr (Or.inl (by simpa using h)))
  · exact hw (Or.inr (Or.inr (Or.inl h)))
  · exact hw (Or.inr (Or.inr (Or.inr h)))
