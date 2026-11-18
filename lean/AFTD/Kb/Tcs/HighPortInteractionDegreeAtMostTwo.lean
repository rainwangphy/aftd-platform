import AFTD.Prelude

/-!
# high_port_interaction_degree_at_most_two

Topic: graphs   Node: ca351f32890a

Provenance: helper lemma. Degree reduction for the high-color implication graph in the matching-based route to OP-874, arXiv:2610.41950.

In a finite simple cubic graph, choose one neighbor at each vertex as its low port. The graph retaining exactly the edges that are high ports at both endpoints has degree at most two at every vertex.
-/

def high_port_interaction_graph {V : Type*} (G : SimpleGraph V) (low : V → V) : SimpleGraph V where
  Adj v w := G.Adj v w ∧ w ≠ low v ∧ v ≠ low w
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (low : V → V) :
    DecidableRel (high_port_interaction_graph G low).Adj := by
  intro v w
  change Decidable (G.Adj v w ∧ w ≠ low v ∧ v ≠ low w)
  infer_instance

theorem high_port_interaction_degree_at_most_two
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcubic : G.IsRegularOfDegree 3) (low : V → V)
    (hlow : ∀ v, G.Adj v (low v)) (v : V) :
    (high_port_interaction_graph G low).degree v ≤ 2 := by
  classical
  have hsub : (high_port_interaction_graph G low).neighborFinset v ⊆
      (G.neighborFinset v).erase (low v) := by
    intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    exact ⟨hw.2.1, hw.1⟩
  calc
    (high_port_interaction_graph G low).degree v =
        ((high_port_interaction_graph G low).neighborFinset v).card := rfl
    _ ≤ ((G.neighborFinset v).erase (low v)).card := Finset.card_le_card hsub
    _ = (G.neighborFinset v).card - 1 := Finset.card_erase_of_mem (by simpa using hlow v)
    _ = 2 := by rw [SimpleGraph.card_neighborFinset_eq_degree, hcubic v]
