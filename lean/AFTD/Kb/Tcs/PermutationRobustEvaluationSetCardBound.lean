import AFTD.Prelude
import AFTD.Kb.Tcs.IsPermutationRobust
import AFTD.Kb.Tcs.DistinctTriplesCard
import AFTD.Kb.Tcs.ThreePointRatioNeZero
import AFTD.Kb.Tcs.ThreePointRatioNeOne
import AFTD.Kb.Tcs.NatCubeBoundOfTriplesLe
import AFTD.Kb.Tcs.DistinctTriples
import AFTD.Kb.Tcs.ThreePointRatio

/-!
# permutation_robust_evaluation_set_card_bound

Topic: information   Node: 81904f4caaee

Provenance: formalization of a published result. Source: arXiv:2611.21275, Proposition 18

Let F be a finite field, and let s ⊆ F be a permutation-robust subset with 3 ≤ s.card. Then s.card * (s.card - 1) * (s.card - 2) ≤ Fintype.card F - 2, and in particular if Fintype.card F = r ^ 3 for some natural number r, then s.card ≤ r + 1.
-/

/-- Proposition 18: Counting upper bound on permutation-robust evaluation sets. -/
theorem permutation_robust_evaluation_set_card_bound {F : Type*} [Field F] [Fintype F] [DecidableEq F] (s : Finset F) (hs : is_permutation_robust s) (hcard : 3 ≤ s.card) : s.card * (s.card - 1) * (s.card - 2) ≤ Fintype.card F - 2 ∧ ∀ (r : ℕ), Fintype.card F = r ^ 3 → s.card ≤ r + 1 := by
  let f : F × F × F → F := fun x => match x with | (a, b, c) => three_point_ratio a b c
  have h_sub : Finset.image f (distinct_triples s) ⊆ ({0, 1} : Finset F)ᶜ := by
    intro y hy
    rw [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or]
    rw [Finset.mem_image] at hy
    rcases hy with ⟨⟨a, b, c⟩, ht, rfl⟩
    dsimp [distinct_triples] at ht
    rw [Finset.mem_filter] at ht
    rcases ht with ⟨-, hab, hac, hbc⟩
    exact ⟨three_point_ratio_ne_zero hab hac, three_point_ratio_ne_one hab hbc⟩
  have h_card_le : (Finset.image f (distinct_triples s)).card ≤ (({0, 1} : Finset F)ᶜ).card :=
    Finset.card_le_card h_sub
  rw [Finset.card_image_of_injOn hs, distinct_triples_card, Finset.card_compl, Finset.card_pair zero_ne_one] at h_card_le
  refine ⟨h_card_le, fun r hr => ?_⟩
  rw [hr] at h_card_le
  exact nat_cube_bound_of_triples_le hcard h_card_le
