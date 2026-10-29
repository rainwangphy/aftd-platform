import AFTD.Prelude
import AFTD.Kb.Tcs.CoronaK1
import AFTD.Kb.Tcs.IsEdgeGeodesicTransversal
import AFTD.Kb.Tcs.CoronaK1MaximalGeodesicEndpoints
import AFTD.Kb.Tcs.IsMaximalGeodesic

/-!
# corona_k1_exists_edge_geodesic_transversal

Topic: graphs   Node: 7cfd32560cb5

Provenance: formalization of a published result. Source: arXiv:2610.36821 Section 5 (The Edge Geodesic Transversal Problem)

For every finite type V with 2 ≤ Fintype.card V and every connected simple graph G on V, there exists a finset S of edges of the corona product corona_k1 G such that is_edge_geodesic_transversal (corona_k1 G) S and S.card = Fintype.card V - 1.
-/

theorem corona_k1_exists_edge_geodesic_transversal_leaf_edge_in_walk {V : Type*} (G : SimpleGraph V) {u : V} {y : V ⊕ V}
    (p : (corona_k1 G).Walk (Sum.inr u) y) (hy : y ≠ Sum.inr u) :
    s(Sum.inl u, Sum.inr u) ∈ p.edges := by
  cases p with
  | nil => contradiction
  | cons h p' =>
    rename_i w
    have hw : w = Sum.inl u := by
      cases w with
      | inl w =>
        have : u = w := h
        rw [this]
      | inr w =>
        exact False.elim h
    subst hw
    rw [Sym2.eq_swap]
    simp [SimpleGraph.Walk.edges]

/-- There exists an edge geodesic transversal of G ⊙ K_1 of cardinality |V| - 1. -/
theorem corona_k1_exists_edge_geodesic_transversal
    {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.Connected) (hn : 2 ≤ Fintype.card V) :
    ∃ S : Finset (Sym2 (V ⊕ V)), is_edge_geodesic_transversal (corona_k1 G) S ∧ S.card = Fintype.card V - 1 := open SimpleGraph in by
  classical
  have : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨w0⟩ := this
  let f : V → Sym2 (V ⊕ V) := fun v => s(Sum.inl v, Sum.inr v)
  have hf_inj : Function.Injective f := by
    intro a b hab
    rw [Sym2.eq_iff] at hab
    rcases hab with ⟨h1, -⟩ | ⟨h1, -⟩
    · cases h1; rfl
    · cases h1
  let S := (Finset.univ.erase w0).image f
  refine ⟨S, ⟨?_, ?_⟩, ?_⟩
  · intro e he
    rw [Finset.mem_image] at he
    obtain ⟨w, -, rfl⟩ := he
    rw [mem_edgeSet]
    show (corona_k1 G).Adj (Sum.inl w) (Sum.inr w)
    rfl
  · intro x y p hp
    have hp_max : is_maximal_geodesic p := ⟨⟨hp.1, hp.2.1⟩, hp.2.2⟩
    obtain ⟨u, v, rfl, rfl, huv⟩ := corona_k1_maximal_geodesic_endpoints G hG hn p hp_max
    by_cases hu : u = w0
    · have hv : v ≠ w0 := by rintro rfl; exact huv hu
      refine ⟨f v, ?_, ?_⟩
      · rw [Finset.mem_image]
        exact ⟨v, Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩, rfl⟩
      · have hx : (Sum.inr u : V ⊕ V) ≠ Sum.inr v := by
          intro h; injection h with h'; exact huv h'
        have h_rev := corona_k1_exists_edge_geodesic_transversal_leaf_edge_in_walk G p.reverse hx
        rw [Walk.edges_reverse, List.mem_reverse] at h_rev
        exact h_rev
    · refine ⟨f u, ?_, ?_⟩
      · rw [Finset.mem_image]
        exact ⟨u, Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩, rfl⟩
      · have hy : (Sum.inr v : V ⊕ V) ≠ Sum.inr u := by
          intro h; injection h with h'; exact huv.symm h'
        exact corona_k1_exists_edge_geodesic_transversal_leaf_edge_in_walk G p hy
  · rw [Finset.card_image_of_injective _ hf_inj]
    rw [Finset.card_erase_of_mem (Finset.mem_univ w0), Fintype.card]
