import AFTD.Prelude

/-!
# simple_graph_common_neighbor_meets_packing_star

Topic: graphs   Node: 94b4e47b2fe2

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign, related to matching-cover reductions in https://arxiv.org/abs/2610.15269; see state/campaigns/triangle_reductions/high_codegree_route_in512.md.

For a triangle-maximal family avoiding an edge, each common neighbor of the edge lies with one endpoint in a family triangle.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_common_neighbor_meets_packing_star
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u v : V) (P : Finset (Finset V)) (huv : G.Adj u v)
    (hmax : ∀ t : Finset V, G.IsNClique 3 t → ∃ s ∈ P, 2 ≤ (s ∩ t).card)
    (havoid : ∀ s ∈ P, ¬(u ∈ s ∧ v ∈ s)) :
    ∀ w : V, G.Adj u w → G.Adj v w → ∃ s ∈ P, w ∈ s ∧ (u ∈ s ∨ v ∈ s) := by
  classical
  intro w huw hvw
  have huwne : u ≠ w := G.ne_of_adj huw
  have hvwne : v ≠ w := G.ne_of_adj hvw
  have huvne : u ≠ v := G.ne_of_adj huv
  let T : Finset V := {u,v,w}
  have hT : G.IsNClique 3 T := by
    rw [SimpleGraph.isNClique_iff]
    constructor
    · intro x hx y hy hxy
      simp only [T, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
      rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
      all_goals first | exact (hxy rfl).elim | exact huv | exact huv.symm | exact huw | exact huw.symm | exact hvw | exact hvw.symm
    · simp [T, huvne, huwne, hvwne, Ne.symm]
  obtain ⟨s, hs, hst⟩ := hmax T hT
  refine ⟨s, hs, ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hst
  have has := (Finset.mem_inter.mp ha).1
  have hbs := (Finset.mem_inter.mp hb).1
  have hat := (Finset.mem_inter.mp ha).2
  have hbt := (Finset.mem_inter.mp hb).2
  simp only [T, Finset.mem_insert, Finset.mem_singleton] at hat hbt
  have hbad := havoid s hs
  rcases hat with rfl | rfl | rfl <;> rcases hbt with rfl | rfl | rfl <;> simp_all
