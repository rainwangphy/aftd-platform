import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumberEqZeroOfCliqueFree

/-!
# simple_graph_triangle_cover_number_delete_edge_le

Topic: graphs   Node: 280107b445ca

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

Deleting an edge e from G decreases the triangle cover number by at most 1: τ(G) ≤ τ(G \ {e}) + 1.
-/

/-- Deleting an edge e from G decreases the triangle cover number by at most 1: τ(G) ≤ τ(G \ {e}) + 1. -/
theorem simple_graph_triangle_cover_number_delete_edge_le {V : Type*} [Fintype V]
    (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    simple_graph_triangle_cover_number G ≤ simple_graph_triangle_cover_number (G.deleteEdges {e}) + 1 := by
  classical
  -- τ(G) is the least cardinality of a triangle cover; take a minimum cover F of G \ {e}.
  set H : SimpleGraph V := G.deleteEdges {e} with hHdef
  -- The family of cardinalities of triangle covers of H is nonempty: the full edge set works.
  have hSne : {n : ℕ | ∃ F : Finset (Sym2 V), (∀ f ∈ F, f ∈ H.edgeSet) ∧
      (∀ t : Finset V, H.IsNClique 3 t → ∃ f ∈ F, ∀ x ∈ f, x ∈ t) ∧ F.card = n}.Nonempty := by
    refine ⟨_, H.edgeFinset, ?_, ?_, rfl⟩
    · intro f hf; rwa [SimpleGraph.mem_edgeFinset] at hf
    · intro t ht
      obtain ⟨u, v, w, huv, -, -, rfl⟩ := Finset.card_eq_three.mp ht.card_eq
      refine ⟨s(u, v), ?_, ?_⟩
      · rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
        exact ht.isClique (by simp) (by simp) huv
      · intro x hx
        rw [Sym2.mem_iff] at hx
        rcases hx with rfl | rfl <;> simp
  obtain ⟨F, hFsub, hFcov, hFcard⟩ := Nat.sInf_mem hSne
  have hFsubG : ∀ f ∈ F, f ∈ G.edgeSet := by
    intro f hf
    have := hFsub f hf
    rw [hHdef, SimpleGraph.edgeSet_deleteEdges] at this
    exact this.1
  -- Adjoining e to F covers every triangle of G.
  have hcoverG : ∀ t : Finset V, G.IsNClique 3 t → ∃ f ∈ insert e F, ∀ x ∈ f, x ∈ t := by
    intro t ht
    by_cases hcase : ∀ x ∈ e, x ∈ t
    · exact ⟨e, Finset.mem_insert_self e F, hcase⟩
    · -- A triangle of G not containing e is a triangle of G \ {e}.
      have hclq : H.IsClique (↑t : Set V) := by
        have hG := ht.isClique
        rw [SimpleGraph.isClique_iff] at hG ⊢
        intro a ha b hb hab
        rw [SimpleGraph.deleteEdges_adj]
        refine ⟨hG ha hb hab, ?_⟩
        intro hmem
        exact hcase fun x hx => by
          rw [← hmem] at hx
          rw [Sym2.mem_iff] at hx
          rcases hx with rfl | rfl <;> assumption
      obtain ⟨f, hfF, hft⟩ := hFcov t ⟨hclq, ht.card_eq⟩
      exact ⟨f, Finset.mem_insert_of_mem hfF, hft⟩
  have hsubG' : ∀ f ∈ insert e F, f ∈ G.edgeSet := by
    intro f hf
    rw [Finset.mem_insert] at hf
    rcases hf with rfl | hf
    · exact he
    · exact hFsubG f hf
  have hmemG : (insert e F).card ∈ {n : ℕ | ∃ F : Finset (Sym2 V), (∀ f ∈ F, f ∈ G.edgeSet) ∧
      (∀ t : Finset V, G.IsNClique 3 t → ∃ f ∈ F, ∀ x ∈ f, x ∈ t) ∧ F.card = n} :=
    ⟨insert e F, hsubG', hcoverG, rfl⟩
  have h1 : simple_graph_triangle_cover_number G ≤ (insert e F).card := Nat.sInf_le hmemG
  have h3 : F.card = simple_graph_triangle_cover_number H := hFcard
  have h2 : (insert e F).card ≤ simple_graph_triangle_cover_number H + 1 := by
    rw [← h3]
    exact Finset.card_insert_le e F
  rw [hHdef] at h2 ⊢
  omega
