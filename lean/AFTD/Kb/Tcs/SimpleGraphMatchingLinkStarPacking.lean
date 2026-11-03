import AFTD.Prelude

/-!
# simple_graph_matching_link_star_packing

Topic: graphs   Node: 8a4f60e74b6a

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

Disjoint two-vertex edges in a vertex link yield a same-size edge-disjoint triangle packing through the vertex.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_matching_link_star_packing
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (z : V) (M : Finset (Finset V))
    (hM : ∀ e ∈ M, e.card = 2 ∧ (∀ x ∈ e, G.Adj z x) ∧
      (∀ x ∈ e, ∀ y ∈ e, x ≠ y → G.Adj x y))
    (hdis : (M : Set (Finset V)).Pairwise Disjoint) :
    (∀ t ∈ M.image (fun e => insert z e), G.IsNClique 3 t) ∧
    ((M.image (fun e => insert z e) : Finset (Finset V)) : Set (Finset V)).Pairwise
      (fun s t => (s ∩ t).card ≤ 1) ∧
    (M.image (fun e => insert z e)).card = M.card := by
  classical
  have hnz : ∀ e ∈ M, z ∉ e := by
    intro e he hz
    have hz' := (hM e he).2.1 z hz
    exact G.irrefl hz'
  constructor
  · intro t ht
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ht
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro a ha b hb hab
      simp only [Finset.mem_coe, Finset.mem_insert] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · exact (hab rfl).elim
      · exact (hM e he).2.1 b hb
      · exact ((hM e he).2.1 a ha).symm
      · exact (hM e he).2.2 a ha b hb hab
    · rw [Finset.card_insert_of_notMem (hnz e he), (hM e he).1]
  constructor
  · intro s hs t ht hst
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp ht
    have hef : e ≠ f := by
      intro h
      apply hst
      exact congrArg (fun q : Finset V => insert z q) h
    have hefdis : Disjoint e f := hdis he hf hef
    have hsub : insert z e ∩ insert z f ⊆ {z} := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_insert] at hx
      simp only [Finset.mem_singleton]
      rcases hx.1 with rfl | hxe
      · rfl
      · rcases hx.2 with rfl | hxf
        · rfl
        · exact False.elim (Finset.disjoint_left.mp hefdis hxe hxf)
    exact (Finset.card_le_card hsub).trans (by simp)
  · apply Finset.card_image_iff.mpr
    intro e he f hf heq
    have hh := congrArg (fun s : Finset V => s.erase z) heq
    simpa [hnz e he, hnz f hf] using hh
