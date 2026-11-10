import AFTD.Prelude
import AFTD.Kb.Tcs.IsUncomplemented
import AFTD.Kb.Tcs.StronglyIncomparable

/-!
# op_1370_case_n3_t3

Topic: combinatorics   Node: 26ec48f43124

Provenance: original. Related work: arXiv:2611.12199 Conjecture 4.3

Base case `n = 3, t = 3` of Conjecture 4.3 of arXiv:2611.12199 (OP-1370): if `𝒜 : Fin 3 → Finset (Finset (Fin 3))` is a family such that each `𝒜 i` is non-empty and uncomplemented, and `𝒜` is strongly incomparable, then `∑ i : Fin 3, (𝒜 i).card ≤ 3`.
-/

open Finset

lemma op_1370_case_n3_t3_exists_third (i j : Fin 3) (hij : i ≠ j) : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  fin_cases i <;> fin_cases j <;> try contradiction
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨0, by decide, by decide⟩

lemma op_1370_case_n3_t3_no_card_one_and_two_ne (𝒜 : Fin 3 → Finset (Finset (Fin 3)))
    (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜)
    (i j : Fin 3) (hij : i ≠ j) {A B : Finset (Fin 3)}
    (hA : A ∈ 𝒜 i) (hB : B ∈ 𝒜 j) (hAc : A.card = 1) (hBc : B.card = 2) :
    False := by
  obtain ⟨x, hx⟩ := card_eq_one.mp hAc
  have hx_not_in_B : x ∉ B := by
    intro hx_in_B
    have : A ⊆ B := by
      rw [hx]
      exact singleton_subset_iff.mpr hx_in_B
    exact hinc i j hij A hA B hB this
  have hB_eq : B = {x}ᶜ := by
    have hsub : B ⊆ {x}ᶜ := by
      intro y hy
      simp only [mem_compl, mem_singleton]
      rintro rfl
      exact hx_not_in_B hy
    have hcard_compl : ({x}ᶜ : Finset (Fin 3)).card = 2 := by
      simp [card_compl]
    exact eq_of_subset_of_card_le hsub (by rw [hBc, hcard_compl])
  obtain ⟨k, hki, hkj⟩ := op_1370_case_n3_t3_exists_third i j hij
  obtain ⟨C, hC⟩ := hne k
  have hx_not_in_C : x ∉ C := by
    intro hx_in_C
    have : A ⊆ C := by
      rw [hx]
      exact singleton_subset_iff.mpr hx_in_C
    exact hinc i k hki.symm A hA C hC this
  have hC_sub_B : C ⊆ B := by
    rw [hB_eq]
    intro y hy
    simp only [mem_compl, mem_singleton]
    rintro rfl
    exact hx_not_in_C hy
  exact hinc k j hkj C hC B hB hC_sub_B

lemma op_1370_case_n3_t3_card_mem_eq_one_or_two (𝒜 : Fin 3 → Finset (Finset (Fin 3)))
    (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜)
    (i : Fin 3) {A : Finset (Fin 3)} (hA : A ∈ 𝒜 i) :
    A.card = 1 ∨ A.card = 2 := by
  have hle : A.card ≤ 3 := by
    have := A.card_le_univ
    simpa using this
  have : A.card = 0 ∨ A.card = 1 ∨ A.card = 2 ∨ A.card = 3 := by omega
  rcases this with h | h | h | h
  · have : A = ∅ := card_eq_zero.mp h
    subst this
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, i ≠ j := by fin_cases i <;> decide
    obtain ⟨B, hB⟩ := hne j
    exact False.elim (hinc i j hj ∅ hA B hB (empty_subset B))
  · left; exact h
  · right; exact h
  · have : A = univ := eq_univ_of_card A (by simpa using h)
    subst this
    obtain ⟨j, hj⟩ : ∃ j : Fin 3, j ≠ i := by fin_cases i <;> decide
    obtain ⟨B, hB⟩ := hne j
    exact False.elim (hinc j i hj B hB univ hA (subset_univ B))

lemma op_1370_case_n3_t3_no_card_one_and_two (𝒜 : Fin 3 → Finset (Finset (Fin 3)))
    (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜)
    (i j : Fin 3) {A B : Finset (Fin 3)}
    (hA : A ∈ 𝒜 i) (hB : B ∈ 𝒜 j) (hAc : A.card = 1) (hBc : B.card = 2) :
    False := by
  by_cases hij : i = j
  · subst hij
    obtain ⟨k, hk⟩ : ∃ k : Fin 3, k ≠ i := by fin_cases i <;> decide
    obtain ⟨C, hC⟩ := hne k
    rcases op_1370_case_n3_t3_card_mem_eq_one_or_two 𝒜 hne hinc k hC with hC1 | hC2
    · exact op_1370_case_n3_t3_no_card_one_and_two_ne 𝒜 hne hinc k i hk hC hB hC1 hBc
    · exact op_1370_case_n3_t3_no_card_one_and_two_ne 𝒜 hne hinc i k hk.symm hA hC hAc hC2
  · exact op_1370_case_n3_t3_no_card_one_and_two_ne 𝒜 hne hinc i j hij hA hB hAc hBc

lemma op_1370_case_n3_t3_all_one_or_all_two (𝒜 : Fin 3 → Finset (Finset (Fin 3)))
    (hne : ∀ i, (𝒜 i).Nonempty) (hinc : strongly_incomparable 𝒜) :
    (∀ i, ∀ A ∈ 𝒜 i, A.card = 1) ∨ (∀ i, ∀ A ∈ 𝒜 i, A.card = 2) := by
  obtain ⟨S, hS⟩ := hne 0
  rcases op_1370_case_n3_t3_card_mem_eq_one_or_two 𝒜 hne hinc 0 hS with hS1 | hS2
  · left
    intro i A hA
    rcases op_1370_case_n3_t3_card_mem_eq_one_or_two 𝒜 hne hinc i hA with hA1 | hA2
    · exact hA1
    · exact False.elim (op_1370_case_n3_t3_no_card_one_and_two 𝒜 hne hinc 0 i hS hA hS1 hA2)
  · right
    intro i A hA
    rcases op_1370_case_n3_t3_card_mem_eq_one_or_two 𝒜 hne hinc i hA with hA1 | hA2
    · exact False.elim (op_1370_case_n3_t3_no_card_one_and_two 𝒜 hne hinc i 0 hA hS hA1 hS2)
    · exact hA2

/-- Base case n = 3, t = 3 of OP-1370: three non-empty uncomplemented strongly incomparable families of subsets of [3] have total size at most 3. -/
theorem op_1370_case_n3_t3 (𝒜 : Fin 3 → Finset (Finset (Fin 3))) (hne : ∀ i, (𝒜 i).Nonempty) (hunc : ∀ i, is_uncomplemented (𝒜 i)) (hinc : strongly_incomparable 𝒜) : ∑ i, (𝒜 i).card ≤ 3 := by
  have _ := hunc
  have hdisj : ((Finset.univ : Finset (Fin 3)) : Set (Fin 3)).PairwiseDisjoint 𝒜 := by
    intro i _ j _ hij
    change Disjoint (𝒜 i) (𝒜 j)
    rw [Finset.disjoint_iff_ne]
    intro A hAi B hAj
    rintro rfl
    exact hinc i j hij A hAi A hAj subset_rfl
  have heq : (Finset.univ.biUnion 𝒜).card = ∑ i, (𝒜 i).card := Finset.card_biUnion hdisj
  rw [← heq]
  rcases op_1370_case_n3_t3_all_one_or_all_two 𝒜 hne hinc with h1 | h2
  · have hsub : Finset.univ.biUnion 𝒜 ⊆ Finset.powersetCard 1 (Finset.univ : Finset (Fin 3)) := by
      intro A hA
      rw [Finset.mem_biUnion] at hA
      obtain ⟨i, -, hi⟩ := hA
      rw [Finset.mem_powersetCard_univ]
      exact h1 i A hi
    have hle := Finset.card_le_card hsub
    have hpow : (Finset.powersetCard 1 (Finset.univ : Finset (Fin 3))).card = 3 := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      rfl
    omega
  · have hsub : Finset.univ.biUnion 𝒜 ⊆ Finset.powersetCard 2 (Finset.univ : Finset (Fin 3)) := by
      intro A hA
      rw [Finset.mem_biUnion] at hA
      obtain ⟨i, -, hi⟩ := hA
      rw [Finset.mem_powersetCard_univ]
      exact h2 i A hi
    have hle := Finset.card_le_card hsub
    have hpow : (Finset.powersetCard 2 (Finset.univ : Finset (Fin 3))).card = 3 := by
      rw [Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
      rfl
    omega
