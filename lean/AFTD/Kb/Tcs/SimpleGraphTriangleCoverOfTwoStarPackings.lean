import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleCoverNumber

/-!
# simple_graph_triangle_cover_of_two_star_packings

Topic: graphs   Node: 915e7742da71

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

Two triangle-maximal families whose non-star edges lie in C give a triangle cover of size at most |C|+1 if their star centers are adjacent.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem simple_graph_triangle_cover_of_two_star_packings
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (u v : V) (P Q : Finset (Finset V)) (C : Finset (Sym2 V))
    (huv : G.Adj u v)
    (hC : ∀ e ∈ C, e ∈ G.edgeSet)
    (hPmax : ∀ t : Finset V, G.IsNClique 3 t → ∃ s ∈ P, 2 ≤ (s ∩ t).card)
    (hQmax : ∀ t : Finset V, G.IsNClique 3 t → ∃ s ∈ Q, 2 ≤ (s ∩ t).card)
    (hPstar : ∀ s ∈ P, ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a = u ∨ b = u ∨ s(a,b) ∈ C)
    (hQstar : ∀ s ∈ Q, ∀ a ∈ s, ∀ b ∈ s, a ≠ b → a = v ∨ b = v ∨ s(a,b) ∈ C) :
    simple_graph_triangle_cover_number G ≤ C.card + 1 := by
  classical
  let F : Finset (Sym2 V) := insert s(u,v) C
  have hFedge : ∀ e ∈ F, e ∈ G.edgeSet := by
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact huv
    · exact hC e he
  have hFcover : ∀ t : Finset V, G.IsNClique 3 t → ∃ e ∈ F, ∀ x ∈ e, x ∈ t := by
    intro t ht
    by_cases hCT : ∃ e ∈ C, ∀ x ∈ e, x ∈ t
    · obtain ⟨e, he, ht⟩ := hCT
      exact ⟨e, Finset.mem_insert_of_mem he, ht⟩
    · have hu : u ∈ t := by
        obtain ⟨s, hs, hst⟩ := hPmax t ht
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hst
        have ha' := Finset.mem_inter.mp ha
        have hb' := Finset.mem_inter.mp hb
        rcases hPstar s hs a ha'.1 b hb'.1 hab with rfl | rfl | he
        · exact ha'.2
        · exact hb'.2
        · exfalso
          apply hCT
          refine ⟨s(a,b), he, ?_⟩
          intro x hx
          rw [Sym2.mem_iff] at hx
          rcases hx with rfl | rfl
          · exact ha'.2
          · exact hb'.2
      have hv : v ∈ t := by
        obtain ⟨s, hs, hst⟩ := hQmax t ht
        obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hst
        have ha' := Finset.mem_inter.mp ha
        have hb' := Finset.mem_inter.mp hb
        rcases hQstar s hs a ha'.1 b hb'.1 hab with rfl | rfl | he
        · exact ha'.2
        · exact hb'.2
        · exfalso
          apply hCT
          refine ⟨s(a,b), he, ?_⟩
          intro x hx
          rw [Sym2.mem_iff] at hx
          rcases hx with rfl | rfl
          · exact ha'.2
          · exact hb'.2
      refine ⟨s(u,v), Finset.mem_insert_self _ _, ?_⟩
      intro x hx
      rw [Sym2.mem_iff] at hx
      rcases hx with rfl | rfl <;> assumption
  calc
    simple_graph_triangle_cover_number G ≤ F.card := Nat.sInf_le ⟨F, hFedge, hFcover, rfl⟩
    _ ≤ C.card + 1 := by simpa [F, Nat.add_comm] using (Finset.card_insert_le s(u,v) C)
