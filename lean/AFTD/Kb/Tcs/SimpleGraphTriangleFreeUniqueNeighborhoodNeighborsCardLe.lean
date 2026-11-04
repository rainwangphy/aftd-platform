import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleFreePrivateNeighborhoodNeighborUnique

/-!
# simple_graph_triangle_free_unique_neighborhood_neighbors_card_le

Topic: combinatorics   Node: 616c3f15de00

Provenance: helper lemma. Private-neighbor obstruction for OP-926, derived from neighborhood matching.

In a finite triangle-free graph with no independent k-set, if v has degree k − 1, then any finite set of vertices each having exactly one neighbor in the neighborhood of v has at most degree(v) vertices.
-/

theorem simple_graph_triangle_free_unique_neighborhood_neighbors_card_le {α : Type*} [Fintype α]
    (G : SimpleGraph α) [DecidableRel G.Adj] (k : ℕ)
    (htri : G.CliqueFree 3) (hfree : Gᶜ.CliqueFree k)
    (v : α) (hdegree : G.degree v + 1 = k) (P : Finset α)
    (hP : ∀ x ∈ P, ∃! w, G.Adj v w ∧ G.Adj w x) : P.card ≤ G.degree v := by
  classical
  let f : α → α := fun x => if h : ∃ w, G.Adj v w ∧ G.Adj w x then Classical.choose h else x
  have hf_mem : ∀ x ∈ P, G.Adj v (f x) ∧ G.Adj (f x) x := by
    intro x hx
    have hex : ∃ w, G.Adj v w ∧ G.Adj w x := (hP x hx).exists
    have hf : f x = Classical.choose hex := by
      simp only [f]
      rw [dif_pos hex]
    rw [hf]
    exact Classical.choose_spec hex
  have hf_inj : Set.InjOn f ↑P := by
    intro x hx y hy hxy
    have hx' : G.Adj v (f x) ∧ G.Adj (f x) x := hf_mem x hx
    have hy' : G.Adj v (f y) ∧ G.Adj (f y) y := hf_mem y hy
    have huniqx : ∀ z, G.Adj v z → G.Adj z x → z = f y := by
      intro z hvz hzx
      obtain ⟨w0, hw0, huniq0⟩ := hP x hx
      have h1 : f x = w0 := huniq0 (f x) ⟨hx'.1, hx'.2⟩
      have h2 : z = w0 := huniq0 z ⟨hvz, hzx⟩
      rw [h2, ← h1, hxy]
    have huniqy : ∀ z, G.Adj v z → G.Adj z y → z = f y := by
      intro z hvz hzy
      obtain ⟨w0, hw0, huniq0⟩ := hP y hy
      have h1 : f y = w0 := huniq0 (f y) ⟨hy'.1, hy'.2⟩
      have h2 : z = w0 := huniq0 z ⟨hvz, hzy⟩
      rw [h2, h1]
    exact simple_graph_triangle_free_private_neighborhood_neighbor_unique G k htri hfree v (f y) x y hdegree hy'.1 (by rw [← hxy]; exact hx'.2) hy'.2 huniqx huniqy
  have himage : P.image f ⊆ G.neighborFinset v := by
    intro w hw
    rw [Finset.mem_image] at hw
    obtain ⟨x, hxP, rfl⟩ := hw
    exact (SimpleGraph.mem_neighborFinset G v (f x)).mpr (hf_mem x hxP).1
  calc P.card = (P.image f).card := (Finset.card_image_of_injOn hf_inj).symm
    _ ≤ (G.neighborFinset v).card := Finset.card_le_card himage
    _ = G.degree v := SimpleGraph.card_neighborFinset_eq_degree G v
