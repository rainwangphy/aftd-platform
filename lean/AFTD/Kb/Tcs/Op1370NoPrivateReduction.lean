import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370PrivateElementBound
import AFTD.Kb.Tcs.Op1370PrivateAbsenceBound

/-!
# op_1370_no_private_reduction

Topic: combinatorics   Node: da18ba633fde

Provenance: helper lemma. Reduction from OP-1370 to op_1370_no_private_stability, using the private-element theorem and its complement-dual.

For at least three nonempty, uncomplemented, mutually strongly incomparable families, the conjectured bound follows if it holds with a two-unit deficit whenever each ground element occurs in at least two families and is absent in at least two families.
-/

open Finset
set_option maxHeartbeats 800000

theorem op_1370_no_private_reduction (n t : ℕ) (ht : 3 ≤ t) (𝒜 : Fin t → Finset (Finset (Fin n))) (hne : ∀ i, (𝒜 i).Nonempty) (hunc : ∀ i, is_uncomplemented (𝒜 i)) (hinc : strongly_incomparable 𝒜) (hcore : (∀ x, ∃ i j : Fin t, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 j, x ∈ T)) → (∀ x, ∃ i j : Fin t, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∉ S) ∧ (∃ T ∈ 𝒜 j, x ∉ T)) → (∑ i, (𝒜 i).card ≤ 2 ^ (n - 1) - 2)) : ∑ i, (𝒜 i).card ≤ 2 ^ (n - 1) - 1 := by
  classical
  by_cases hp : ∀ x, ∃ i j : Fin t, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∈ S) ∧ (∃ T ∈ 𝒜 j, x ∈ T)
  · by_cases hn : ∀ x, ∃ i j : Fin t, i ≠ j ∧ (∃ S ∈ 𝒜 i, x ∉ S) ∧ (∃ T ∈ 𝒜 j, x ∉ T)
    · have h := hcore hp hn
      omega
    · obtain ⟨x, hx⟩ := not_forall.mp hn
      by_cases hex : ∃ i : Fin t, ∃ S ∈ 𝒜 i, x ∉ S
      · obtain ⟨i, S, hS, hxs⟩ := hex
        apply op_1370_private_absence_bound n t ht 𝒜 hne hinc i x (hunc i)
        intro j hji T hT
        by_contra hxt
        exact hx ⟨i, j, hji.symm, ⟨S, hS, hxs⟩, ⟨T, hT, hxt⟩⟩
      · let i : Fin t := ⟨0, by omega⟩
        apply op_1370_private_absence_bound n t ht 𝒜 hne hinc i x (hunc i)
        intro j hji T hT
        by_contra hxt
        exact hex ⟨j, T, hT, hxt⟩
  · obtain ⟨x, hx⟩ := not_forall.mp hp
    by_cases hex : ∃ i : Fin t, ∃ S ∈ 𝒜 i, x ∈ S
    · obtain ⟨i, S, hS, hxs⟩ := hex
      apply op_1370_private_element_bound n t ht 𝒜 hne hinc i x (hunc i)
      intro j hji T hT hxt
      exact hx ⟨i, j, hji.symm, ⟨S, hS, hxs⟩, ⟨T, hT, hxt⟩⟩
    · let i : Fin t := ⟨0, by omega⟩
      apply op_1370_private_element_bound n t ht 𝒜 hne hinc i x (hunc i)
      intro j hji T hT hxt
      exact hex ⟨j, T, hT, hxt⟩
