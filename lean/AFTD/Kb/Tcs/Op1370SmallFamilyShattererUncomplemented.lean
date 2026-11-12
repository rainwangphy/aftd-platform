import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented

/-!
# op_1370_small_family_shatterer_uncomplemented

Topic: combinatorics   Node: 26c941c40765

Provenance: helper lemma. Trace-counting reduction for arXiv:2611.12199, Conjecture 4.3.

If a family of subsets of Fin n has fewer than 2^ceil(n/2) members, then its family of shattered sets contains no complementary pair.
-/

open Finset
set_option maxHeartbeats 1000000

lemma op1370_local_shattered_card_lower (n : ℕ) (F : Finset (Finset (Fin n)))
    (S : Finset (Fin n)) (hS : S ∈ F.shatterer) : 2 ^ S.card ≤ F.card := by
  have hs : F.image (fun T => S ∩ T) = S.powerset :=
    Finset.shatters_iff.mp (Finset.mem_shatterer.mp hS)
  have h := Finset.card_image_le (s := F) (f := fun T => S ∩ T)
  rw [hs, Finset.card_powerset] at h
  exact h

theorem op_1370_small_family_shatterer_uncomplemented (n : ℕ) (F : Finset (Finset (Fin n))) (hsmall : F.card < 2 ^ ((n + 1) / 2)) : is_uncomplemented F.shatterer := by
  classical
  intro S hS hSc
  have hs := op1370_local_shattered_card_lower n F S hS
  have hsc := op1370_local_shattered_card_lower n F Sᶜ hSc
  have hSn : S.card ≤ n := by simpa using Finset.card_le_univ S
  have hsum : S.card + (Sᶜ).card = n := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  by_cases hle : (n + 1) / 2 ≤ S.card
  · have hp : 2 ^ ((n + 1) / 2) ≤ 2 ^ S.card := by gcongr <;> omega
    omega
  · have hle' : (n + 1) / 2 ≤ (Sᶜ).card := by omega
    have hp : 2 ^ ((n + 1) / 2) ≤ 2 ^ (Sᶜ).card := by gcongr <;> omega
    omega
