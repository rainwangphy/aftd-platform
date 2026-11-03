import AFTD.Prelude
import AFTD.Kb.Tcs.LinearBookForcesCenter

/-!
# linear_family_high_degree_neighborhood_obstruction

Topic: graphs   Node: 1138b1e9cf96

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

In a finite linear family, if B has more than q points and each point of B lies in more than q members, every set hitting all members that meet B has more than q points.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem linear_family_high_degree_neighborhood_obstruction {α : Type*} [DecidableEq α]
    (H : Finset (Finset α)) (B C : Finset α) (q : ℕ)
    (hl : ∀ A ∈ H, ∀ D ∈ H, A ≠ D → (A ∩ D).card ≤ 1)
    (hB : q < B.card)
    (hdeg : ∀ b ∈ B, q < (H.filter (fun A => b ∈ A)).card)
    (hcover : ∀ A ∈ H, ¬Disjoint A B → ¬Disjoint A C) : q < C.card := by
  classical
  by_contra hn
  have hc : C.card ≤ q := Nat.le_of_not_gt hn
  have hsub : B ⊆ C := by
    intro b hb
    let Q := H.filter (fun A => b ∈ A)
    apply linear_book_forces_center Q b C
    · intro A hA
      exact (Finset.mem_filter.mp hA).2
    · intro A hA D hD hAD
      exact hl A (Finset.mem_filter.mp hA).1 D (Finset.mem_filter.mp hD).1 hAD
    · intro A hA
      have h := Finset.mem_filter.mp hA
      apply hcover A h.1
      exact Finset.not_disjoint_iff.mpr ⟨b, h.2, hb⟩
    · exact lt_of_le_of_lt hc (hdeg b hb)
  have hcard := Finset.card_le_card hsub
  omega
