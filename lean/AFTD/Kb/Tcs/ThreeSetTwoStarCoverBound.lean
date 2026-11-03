import AFTD.Prelude

/-!
# three_set_two_star_cover_bound

Topic: graphs   Node: 0054c8874646

Provenance: helper lemma. Structural helper for the triangle packing-cover campaign; related matching-cover reductions are in https://arxiv.org/abs/2610.15269, Lemma 2.3. Finite checks and limitations are recorded in state/campaigns/triangle_reductions/high_codegree_route_in512.md.

Three-element sets covering outside points through either of two fixed centers cover at most twice as many points as there are sets.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem three_set_two_star_cover_bound {α : Type*} [DecidableEq α]
    (P : Finset (Finset α)) (N : Finset α) (u v : α)
    (hsize : ∀ t ∈ P, t.card = 3)
    (hN : ∀ w ∈ N, w ≠ u ∧ w ≠ v ∧
      ∃ t ∈ P, w ∈ t ∧ (u ∈ t ∨ v ∈ t)) :
    N.card ≤ 2 * P.card := by
  classical
  let F (t : Finset α) : Finset α :=
    if u ∈ t then t.erase u else if v ∈ t then t.erase v else ∅
  have hF : ∀ t ∈ P, (F t).card ≤ 2 := by
    intro t ht
    by_cases hu : u ∈ t
    · simp [F, hu, Finset.card_erase_of_mem hu, hsize t ht]
    · by_cases hv : v ∈ t
      · simp [F, hu, hv, Finset.card_erase_of_mem hv, hsize t ht]
      · simp [F, hu, hv]
  have hsub : N ⊆ P.biUnion F := by
    intro w hw
    obtain ⟨hwu, hwv, t, ht, hwt, hct⟩ := hN w hw
    apply Finset.mem_biUnion.mpr
    refine ⟨t, ht, ?_⟩
    rcases hct with hu | hv
    · simp [F, hu, hwt, hwu]
    · by_cases hu : u ∈ t
      · simp [F, hu, hwt, hwu]
      · simp [F, hu, hv, hwt, hwv]
  calc
    N.card ≤ (P.biUnion F).card := Finset.card_le_card hsub
    _ ≤ ∑ t ∈ P, (F t).card := Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ P, 2 := by exact Finset.sum_le_sum hF
    _ = 2 * P.card := by simp [Nat.mul_comm]
