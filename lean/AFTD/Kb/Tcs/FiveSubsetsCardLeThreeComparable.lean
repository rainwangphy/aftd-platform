import AFTD.Prelude

/-!
# five_subsets_card_le_three_comparable

Topic: combinatorics   Node: c033527ee4a2

Provenance: helper lemma. step towards op_270_five_diamond_poset_ramsey_number

Five subsets of a set with at most three elements cannot be pairwise incomparable: two of them are nested.
-/

/-- Sperner bound for a 3-element ground set: five subsets of a set of size at most 3 contain two comparable members. -/
theorem five_subsets_card_le_three_comparable {α : Type*} [DecidableEq α]
    (X : Finset α) (hX : X.card ≤ 3) (M : Fin 5 → Finset α) (hM : ∀ i, M i ⊆ X) :
    ∃ i i', i ≠ i' ∧ (M i ⊆ M i' ∨ M i' ⊆ M i) := by
  by_contra h
  push Not at h
  let β := ↥X
  let N : Fin 5 → Finset β := fun i => (M i).subtype (· ∈ X)
  have hN_inj : Function.Injective N := by
    intro i j hij
    have hM_eq : M i = M j := by
      rw [← Finset.subtype_map_of_mem (hM i), ← Finset.subtype_map_of_mem (hM j)]
      exact congrArg (Finset.map (Function.Embedding.subtype _)) hij
    by_contra hne
    exact (h i j hne).1 (hM_eq ▸ Finset.Subset.rfl)
  set 𝒜 : Finset (Finset β) := Finset.univ.image N
  have h_card : 𝒜.card = 5 := by
    rw [Finset.card_image_of_injective _ hN_inj]
    simp
  have h_anti : IsAntichain (fun x1 x2 => x1 ⊆ x2) (𝒜 : Set (Finset β)) := by
    intro A hA B hB hne
    change A ∈ Finset.univ.image N at hA
    change B ∈ Finset.univ.image N at hB
    rw [Finset.mem_image] at hA hB
    rcases hA with ⟨i, -, rfl⟩
    rcases hB with ⟨j, -, rfl⟩
    have hij : i ≠ j := by
      rintro rfl
      exact hne rfl
    intro hsub
    have hM_sub : M i ⊆ M j := by
      intro x hx
      have hxX : x ∈ X := hM i hx
      have hxN : (⟨x, hxX⟩ : β) ∈ N i := by
        dsimp [N]
        rw [Finset.mem_subtype]
        exact hx
      have := hsub hxN
      dsimp [N] at this
      rw [Finset.mem_subtype] at this
      exact this
    exact (h i j hij).1 hM_sub
  have hsperner := IsAntichain.sperner h_anti
  have hcard_beta : Fintype.card β = X.card := Fintype.card_coe X
  rw [hcard_beta, h_card] at hsperner
  have hchoose : X.card.choose (X.card / 2) ≤ 3 := by
    interval_cases X.card <;> decide
  omega
