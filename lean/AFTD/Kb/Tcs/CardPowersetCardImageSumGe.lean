import AFTD.Prelude

/-!
# card_powersetCard_image_sum_ge

Topic: combinatorics   Node: 1862153da2ab

Provenance: helper lemma. arXiv:2610.34372, Proof of Lemma 2.1

For any finite set A of natural numbers and any k ≤ |A|, the number of distinct sums of k-element subsets of A is at least k(|A| - k) + 1.
-/

/-- For any finite set of integers and 0 <= k <= |A|, the number of k-element subset sums is at least k(|A| - k) + 1. -/
theorem card_powersetCard_image_sum_ge (A : Finset ℕ) (k : ℕ) (hk : k ≤ A.card) :
    k * (A.card - k) + 1 ≤ ((A.powersetCard k).image (Finset.sum · id)).card := by
  open Finset in
  suffices ∀ (d : ℕ) (A : Finset ℕ) (k : ℕ) (hk : k ≤ A.card) (hd : A.card - k = d),
      k * (A.card - k) + 1 ≤ ((A.powersetCard k).image (Finset.sum · id)).card by
    exact this (A.card - k) A k hk rfl
  intro d
  induction d with
  | zero =>
    intro A k hk hd
    have h_eq : A.card = k := by omega
    subst h_eq
    rw [Finset.powersetCard_self, Finset.image_singleton, Finset.card_singleton]
    rw [Nat.sub_self, mul_zero, zero_add]
  | succ d ih =>
    intro A k hk hd
    by_cases hk0 : k = 0
    · subst hk0
      simp
    have hk_pos : 0 < k := Nat.pos_of_ne_zero hk0
    have hA_pos : 0 < A.card := by omega
    have hA_ne : A.Nonempty := Finset.card_pos.mp hA_pos
    set m := A.max' hA_ne
    have hmA : m ∈ A := A.max'_mem hA_ne
    set A' := A.erase m
    have hA'_card : A'.card = A.card - 1 := Finset.card_erase_of_mem hmA
    have hkA' : k ≤ A'.card := by omega
    have hd' : A'.card - k = d := by omega
    have h_ih := ih A' k hkA' hd'

    have hA'_sub : A' ⊆ A := Finset.erase_subset m A
    set S₁ := (A'.powersetCard k).image (Finset.sum · id)
    have hS₁_sub : S₁ ⊆ (A.powersetCard k).image (Finset.sum · id) :=
      Finset.image_subset_image (Finset.powersetCard_mono hA'_sub)
    have hne₁ : (A'.powersetCard k).Nonempty := Finset.powersetCard_nonempty.mpr hkA'
    have hS₁_ne : S₁.Nonempty := hne₁.image _
    set M := S₁.max' hS₁_ne
    have hM_mem : M ∈ S₁ := S₁.max'_mem hS₁_ne
    rw [Finset.mem_image] at hM_mem
    rcases hM_mem with ⟨T, hT, hM_eq⟩
    rw [Finset.mem_powersetCard] at hT
    have hT_sub : T ⊆ A' := hT.1
    have hT_card : T.card = k := hT.2
    have hM_le : ∀ s ∈ S₁, s ≤ M := fun s hs => Finset.le_max' S₁ s hs

    have hm_notin_A' : m ∉ A' := Finset.notMem_erase m A
    have hm_notin_T : m ∉ T := fun h => hm_notin_A' (hT_sub h)
    have h_lt_m : ∀ x ∈ A', x < m := by
      intro x hx
      have hx_mem : x ∈ A := Finset.mem_of_mem_erase hx
      have hx_ne : x ≠ m := Finset.ne_of_mem_erase hx
      exact lt_of_le_of_ne (Finset.le_max' A x hx_mem) hx_ne

    let Tx (x : ℕ) : Finset ℕ := insert m (T.erase x)
    let f (x : ℕ) : ℕ := (Tx x).sum id

    have h_sum_prop : ∀ x ∈ T, (Tx x) ⊆ A ∧ (Tx x).card = k ∧ f x + x = M + m ∧ M < f x := by
      intro x hx
      have hmTx : m ∉ T.erase x := fun h => hm_notin_T (Finset.mem_of_mem_erase h)
      have h1 : Tx x ⊆ A := by
        intro y hy
        rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hmA
        · exact Finset.mem_of_mem_erase (hT_sub (Finset.mem_of_mem_erase hy))
      have h2 : (Tx x).card = k := by
        dsimp [Tx]
        rw [Finset.card_insert_of_notMem hmTx, Finset.card_erase_of_mem hx, hT_card]
        omega
      have h_ins : (Tx x).sum id = m + (T.erase x).sum id := by
        dsimp [Tx]
        rw [Finset.sum_insert hmTx]
        rfl
      have h_erase : (T.erase x).sum id + x = T.sum id := Finset.sum_erase_add T id hx
      have h3 : f x + x = M + m := by
        dsimp [f]
        omega
      have hx_lt_m : x < m := h_lt_m x (hT_sub hx)
      have h4 : M < f x := by omega
      exact ⟨h1, h2, h3, h4⟩

    have hf_inj : Set.InjOn f T := by
      intro x hx y hy hf_eq
      have hx_sum := (h_sum_prop x hx).2.2.1
      have hy_sum := (h_sum_prop y hy).2.2.1
      omega

    set S₂ := T.image f
    have hS₂_card : S₂.card = k := by
      rw [Finset.card_image_of_injOn hf_inj, hT_card]

    have hS₂_sub : S₂ ⊆ (A.powersetCard k).image (Finset.sum · id) := by
      intro s hs
      rw [Finset.mem_image] at hs
      rcases hs with ⟨x, hx, rfl⟩
      have hprop := h_sum_prop x hx
      rw [Finset.mem_image]
      refine ⟨Tx x, ?_, rfl⟩
      rw [Finset.mem_powersetCard]
      exact ⟨hprop.1, hprop.2.1⟩

    have h_disj : Disjoint S₁ S₂ := by
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      rw [Finset.mem_image] at hx2
      rcases hx2 with ⟨y, hy, rfl⟩
      have h1 := hM_le (f y) hx1
      have h2 := (h_sum_prop y hy).2.2.2
      omega

    have h_union : S₁.card + S₂.card ≤ ((A.powersetCard k).image (Finset.sum · id)).card := by
      have h_sub : S₁ ∪ S₂ ⊆ (A.powersetCard k).image (Finset.sum · id) := Finset.union_subset hS₁_sub hS₂_sub
      have h_card := Finset.card_le_card h_sub
      rw [Finset.card_union_of_disjoint h_disj] at h_card
      exact h_card

    rw [hd]
    have h_split : k * (d + 1) = k * d + k := by ring
    rw [hd'] at h_ih
    omega
