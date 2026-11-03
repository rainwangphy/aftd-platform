import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSetTwoStarCoverBound

/-!
# simple_graph_maximal_packing_common_neighbors_le

Topic: graphs   Node: 7ea3cc6ba22e

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

If a maximal edge-disjoint triangle packing avoids an edge, that edge has at most twice as many common neighbors as the packing has triangles.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_maximal_packing_common_neighbors_le
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v : V) (P : Finset (Finset V))
    (huv : G.Adj u v)
    (hcl : ∀ t ∈ P, G.IsNClique 3 t)
    (hmax : ∀ t : Finset V, G.IsNClique 3 t → ∃ s ∈ P, 2 ≤ (s ∩ t).card)
    (havoid : ∀ s ∈ P, ¬(u ∈ s ∧ v ∈ s)) :
    ((Finset.univ : Finset V).filter (fun w => G.Adj u w ∧ G.Adj v w)).card ≤ 2 * P.card := by
  classical
  let N := (Finset.univ : Finset V).filter (fun w => G.Adj u w ∧ G.Adj v w)
  apply three_set_two_star_cover_bound P N u v
  · intro s hs
    exact (hcl s hs).card_eq
  · intro w hw
    have hw' : G.Adj u w ∧ G.Adj v w := (Finset.mem_filter.mp hw).2
    have huw : u ≠ w := G.ne_of_adj hw'.1
    have hvw : v ≠ w := G.ne_of_adj hw'.2
    have huvne : u ≠ v := G.ne_of_adj huv
    refine ⟨Ne.symm huw, Ne.symm hvw, ?_⟩
    let T : Finset V := {u,v,w}
    have hT : G.IsNClique 3 T := by
      rw [SimpleGraph.isNClique_iff]
      constructor
      · intro x hx y hy hxy
        simp only [T, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hx hy
        rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
        all_goals first | exact (hxy rfl).elim | exact huv | exact huv.symm | exact hw'.1 | exact hw'.1.symm | exact hw'.2 | exact hw'.2.symm
      · simp [T, huvne, huw, hvw, Ne.symm]
    obtain ⟨s, hs, hst⟩ := hmax T hT
    refine ⟨s, hs, ?_⟩
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hst
    have has := (Finset.mem_inter.mp ha).1
    have hbs := (Finset.mem_inter.mp hb).1
    have hat := (Finset.mem_inter.mp ha).2
    have hbt := (Finset.mem_inter.mp hb).2
    simp only [T, Finset.mem_insert, Finset.mem_singleton] at hat hbt
    have hbad := havoid s hs
    rcases hat with rfl | rfl | rfl <;> rcases hbt with rfl | rfl | rfl <;>
      simp_all
