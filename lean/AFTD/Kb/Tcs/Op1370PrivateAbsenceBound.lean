import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable
import AFTD.Kb.Tcs.Op1370PrivateElementBound

/-!
# op_1370_private_absence_bound

Topic: combinatorics   Node: d1332b93d058

Provenance: helper lemma. Complement-dual corollary of op_1370_private_element_bound, for OP-1370.

At least three nonempty mutually strongly incomparable families have total size at most 2^(n-1)-1 if an element occurs in every set outside one designated uncomplemented family.
-/

open Finset
set_option maxHeartbeats 800000

theorem op_1370_private_absence_bound (n t : ℕ) (ht : 3 ≤ t) (𝒜 : Fin t → Finset (Finset (Fin n))) (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜) (i : Fin t) (x : Fin n) (hunc : is_uncomplemented (𝒜 i)) (hx : ∀ j, j ≠ i → ∀ S ∈ 𝒜 j, x ∈ S) : ∑ j, (𝒜 j).card ≤ 2 ^ (n - 1) - 1 := by
  classical
  let ℬ : Fin t → Finset (Finset (Fin n)) := fun j => (𝒜 j).image compl
  have hne' : ∀ j, (ℬ j).Nonempty := by
    intro j
    obtain ⟨S, hS⟩ := hne j
    exact ⟨Sᶜ, mem_image.mpr ⟨S, hS, rfl⟩⟩
  have hinc' : strongly_incomparable ℬ := by
    intro j k hjk S hS T hT hST
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hS
    obtain ⟨B, hB, rfl⟩ := mem_image.mp hT
    have hBA : B ⊆ A := by simpa using hST
    exact hinc k j hjk.symm B hB A hA hBA
  have hunc' : is_uncomplemented (ℬ i) := by
    intro S hS hSc
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hS
    obtain ⟨B, hB, he⟩ := mem_image.mp hSc
    have hBA : B = Aᶜ := by
      have h := congrArg compl he
      simpa using h
    subst B
    exact hunc A hA hB
  have hx' : ∀ j, j ≠ i → ∀ S ∈ ℬ j, x ∉ S := by
    intro j hj S hS
    obtain ⟨A, hA, rfl⟩ := mem_image.mp hS
    simpa using hx j hj A hA
  have h := op_1370_private_element_bound n t ht ℬ hne' hinc' i x hunc' hx'
  have hc : ∀ j, (ℬ j).card = (𝒜 j).card := fun j => card_image_of_injective _ compl_injective
  simp only [hc] at h
  exact h
