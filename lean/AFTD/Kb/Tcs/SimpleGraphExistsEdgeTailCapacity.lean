import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteTwoIncidenceCapacityAssignment

/-!
# simple_graph_exists_edge_tail_capacity

Topic: graphs   Node: c573c193dfa0

Provenance: helper lemma. Helper for OP-494 in arXiv:2610.30174, following the additive-list coloring argument of arXiv:2302.02190v3, Corollary 5.3. Apply the two-incidence capacity lemma to the edge subtype and use the incidence-finset degree bound.

Every finite simple graph of maximum degree at least two admits an assignment of each edge to one of its endpoints, with at most maximum-degree-minus-one edges assigned to any vertex.
-/

open scoped BigOperators

theorem simple_graph_exists_edge_tail_capacity
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hd : 2 ≤ G.maxDegree) :
    ∃ f : G.edgeSet → V, (∀ e : G.edgeSet, f e ∈ (e : Sym2 V)) ∧
      ∀ v, (Finset.univ.filter (fun e => f e = v)).card ≤ G.maxDegree - 1 := by
  classical
  apply finite_two_incidence_capacity_assignment (fun (e : G.edgeSet) v => v ∈ (e : Sym2 V))
    G.maxDegree hd
  · intro e
    have h : Finset.univ.filter (fun v => v ∈ (e : Sym2 V)) = (e : Sym2 V).toFinset := by
      ext v
      simp
    rw [h]
    exact Sym2.card_toFinset_of_not_isDiag _ (G.not_isDiag_of_mem_edgeSet e.property)
  · intro v
    calc
      (Finset.univ.filter (fun e : G.edgeSet => v ∈ (e : Sym2 V))).card ≤
          (G.incidenceFinset v).card := by
        apply Finset.card_le_card_of_injOn (fun e : G.edgeSet => (e : Sym2 V))
        · intro e he
          change (e : Sym2 V) ∈ G.incidenceFinset v
          rw [G.mem_incidenceFinset, G.edge_mem_incidenceSet_iff]
          exact (Finset.mem_filter.mp he).2
        · intro e _ e' _ he
          exact Subtype.ext he
      _ = G.degree v := G.card_incidenceFinset_eq_degree v
      _ ≤ G.maxDegree := G.degree_le_maxDegree v
