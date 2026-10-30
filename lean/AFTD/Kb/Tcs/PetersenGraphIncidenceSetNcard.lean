import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenGraph

/-!
# petersen_graph_incidenceSet_ncard

Topic: np_completeness   Node: 4aa477948146

Provenance: helper lemma. Sanity check of petersen_graph (P10 is cubic), for arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs)

The Petersen graph is cubic: every vertex x of petersen_graph lies in exactly 3 edges, (petersen_graph.incidenceSet x).ncard = 3.
-/

theorem petersen_graph_incidenceSet_ncard (x : {s : Finset (Fin 5) // s.card = 2}) :
    (petersen_graph.incidenceSet x).ncard = 3 := by
  classical
  -- the incidence set of `x` is in bijection with its neighbour set
  have h1 : (petersen_graph.incidenceSet x).ncard = (petersen_graph.neighborSet x).ncard := by
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact Nat.card_congr (SimpleGraph.incidenceSetEquivNeighborSet petersen_graph x)
  rw [h1]
  have h2 : (petersen_graph.neighborSet x).ncard = Fintype.card ↥(petersen_graph.neighborSet x) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
  rw [h2]
  set s : Finset (Fin 5) := x.1
  have hscard : s.card = 2 := x.2
  -- a vertex `t` is a neighbour of `x` iff `t.1 ⊆ sᶜ`, i.e. `t.1 ∈ (sᶜ).powersetCard 2`
  have e : ↥(petersen_graph.neighborSet x) ≃ ↥((sᶜ).powersetCard 2) :=
  { toFun := fun t : ↥(petersen_graph.neighborSet x) => (⟨t.1.1, by
      rw [Finset.mem_powersetCard]
      refine ⟨fun a ha => ?_, t.1.2⟩
      rw [Finset.mem_compl]
      intro hsa
      exact Finset.disjoint_left.mp t.2 hsa ha⟩ : ↥((sᶜ).powersetCard 2))
    invFun := fun u : ↥((sᶜ).powersetCard 2) => (⟨⟨u.1, (Finset.mem_powersetCard.mp u.2).2⟩, by
      change Disjoint (s : Finset (Fin 5)) (u.1 : Finset (Fin 5))
      rw [Finset.disjoint_left]
      intro a hsa hau
      have h : a ∈ sᶜ := (Finset.mem_powersetCard.mp u.2).1 hau
      rw [Finset.mem_compl] at h
      exact h hsa⟩ : ↥(petersen_graph.neighborSet x))
    left_inv := fun t => rfl
    right_inv := fun u => rfl }
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powersetCard, Finset.card_compl, hscard]
  norm_num
