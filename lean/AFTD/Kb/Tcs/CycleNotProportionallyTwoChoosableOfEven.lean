import AFTD.Prelude

/-!
# cycle_not_proportionally_two_choosable_of_even

Topic: graphs   Node: 305954e1de37

Provenance: helper lemma. step towards cycle_not_proportionally_two_choosable

For every even integer n ≥ 3, the simple n-cycle C_n is not proportionally 2-choosable.
-/

open Finset

def cycle_not_prop_testL (n : ℕ) (v : Fin n) : Finset (Fin 3) :=
  if v.val % 2 = 0 then {0, 1} else {0, 2}

lemma cycle_not_prop_testL_card (n : ℕ) (v : Fin n) : (cycle_not_prop_testL n v).card = 2 := by
  dsimp [cycle_not_prop_testL]
  split_ifs <;> decide

lemma cycle_not_prop_card_even (m k : ℕ) (h : m + 2 = 2 * k) :
    (Finset.univ.filter (fun (v : Fin (m + 2)) => v.val % 2 = 0)).card = k := by
  have h_bij := Finset.card_bij (s := (Finset.univ : Finset (Fin k)))
    (t := Finset.univ.filter (fun (v : Fin (m + 2)) => v.val % 2 = 0))
    (i := fun a _ => ⟨2 * a.val, by omega⟩)
    (hi := by
      intro a _
      simp only [mem_filter, mem_univ, true_and]
      omega)
    (i_inj := by
      intro a₁ _ a₂ _ heq
      ext
      have : (⟨2 * a₁.val, by omega⟩ : Fin (m + 2)) = ⟨2 * a₂.val, by omega⟩ := heq
      simp only [Fin.mk.injEq] at this
      omega)
    (i_surj := by
      intro b hb
      simp only [mem_filter, mem_univ, true_and] at hb
      refine ⟨⟨b.val / 2, by omega⟩, mem_univ _, ?_⟩
      ext
      dsimp
      omega)
  rw [← h_bij, card_univ, Fintype.card_fin]

lemma cycle_not_prop_card_odd (m k : ℕ) (h : m + 2 = 2 * k) :
    (Finset.univ.filter (fun (v : Fin (m + 2)) => v.val % 2 ≠ 0)).card = k := by
  have h_compl : (Finset.univ.filter (fun (v : Fin (m + 2)) => v.val % 2 ≠ 0)) =
      (Finset.univ.filter (fun (v : Fin (m + 2)) => v.val % 2 = 0))ᶜ := by
    ext v
    simp [ne_eq]
  rw [h_compl, card_compl, Fintype.card_fin, cycle_not_prop_card_even m k h]
  omega

lemma cycle_not_prop_cycle_adj_succ (n : ℕ) (v : Fin (n + 2)) :
    (SimpleGraph.cycleGraph (n + 2)).Adj v (v + 1) := by
  rw [SimpleGraph.cycleGraph_adj]
  right
  exact add_sub_cancel_left v 1

lemma cycle_not_prop_shift_iff (m : ℕ) (S : Finset (Fin (m + 2))) (k : ℕ)
    (hS_card : S.card = k)
    (hcompl_card : Sᶜ.card = k)
    (h_disj : ∀ u ∈ S, u + 1 ∉ S) :
    ∀ u, (u + 1 ∈ S ↔ u ∉ S) := by
  have himage_sub : S.image (· + 1) ⊆ Sᶜ := by
    intro x hx
    simp only [mem_image] at hx
    rcases hx with ⟨u, hu, rfl⟩
    simp only [mem_compl]
    exact h_disj u hu
  have himage_card : (S.image (· + 1)).card = k := by
    rw [card_image_of_injective S (fun a b h => by simpa using h), hS_card]
  have himage_eq : S.image (· + 1) = Sᶜ := by
    apply eq_of_subset_of_card_le himage_sub
    rw [himage_card, hcompl_card]
  intro u
  constructor
  · intro hu1 hu
    exact h_disj u hu hu1
  · intro hu
    by_contra hu1
    have hmem : u + 1 ∈ Sᶜ := by simpa using hu1
    rw [← himage_eq] at hmem
    simp only [mem_image] at hmem
    rcases hmem with ⟨w, hw, hweq⟩
    have : w = u := by simpa using hweq
    subst this
    exact hu hw

lemma cycle_not_prop_fin_mem_S_iff (m : ℕ) (S : Finset (Fin (m + 2)))
    (h_shift : ∀ u, (u + 1 ∈ S ↔ u ∉ S)) :
    ∀ (v : Fin (m + 2)), v ∈ S ↔ (v.val % 2 = 0 ↔ (0 : Fin (m + 2)) ∈ S) := by
  have h_nat : ∀ j (hj : j < m + 2),
      (⟨j, hj⟩ : Fin (m + 2)) ∈ S ↔ (j % 2 = 0 ↔ (0 : Fin (m + 2)) ∈ S) := by
    intro j
    induction' j with j ih
    · intro hj
      have h0 : (⟨0, hj⟩ : Fin (m + 2)) = 0 := rfl
      rw [h0]
      simp
    · intro hj
      have hj_prev : j < m + 2 := by omega
      have h_succ : (⟨j + 1, hj⟩ : Fin (m + 2)) = (⟨j, hj_prev⟩ : Fin (m + 2)) + 1 := by
        ext
        simp only [Fin.val_add, Fin.val_one]
        rw [Nat.mod_eq_of_lt hj]
      rw [h_succ, h_shift, ih hj_prev]
      have : (j + 1) % 2 = 0 ↔ ¬ (j % 2 = 0) := by omega
      tauto
  intro v
  exact h_nat v.val v.isLt

/-- Even cycles C_n (n ≥ 3) are not proportionally 2-choosable. -/
theorem cycle_not_proportionally_two_choosable_of_even (n : ℕ) (hn : 3 ≤ n) (heven : Even n) :
    ¬ ∀ (α : Type) [Fintype α] [DecidableEq α] (L : Fin n → Finset α),
      (∀ v, (L v).card = 2) →
      ∃ f : (SimpleGraph.cycleGraph n).Coloring α,
        (∀ v, f v ∈ L v) ∧
        ∀ c : α,
          let η := (Finset.univ.filter (fun v => c ∈ L v)).card
          let uses := (Finset.univ.filter (fun v => f v = c)).card
          uses = η / 2 ∨ uses = η ⌈/⌉ 2 := by
  intro h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, m + 2 = 2 * k := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k, by omega⟩
  have hk2 : 2 ≤ k := by omega
  have h_lists := cycle_not_prop_testL_card (m + 2)
  obtain ⟨f, hf_list, hf_uses⟩ := h (Fin 3) (cycle_not_prop_testL (m + 2)) h_lists
  let S := Finset.univ.filter (fun (v : Fin (m + 2)) => f v = 0)
  have hmem_S (v : Fin (m + 2)) : v ∈ S ↔ f v = 0 := by simp [S]
  have hη0 : (Finset.univ.filter (fun (v : Fin (m + 2)) => (0 : Fin 3) ∈ cycle_not_prop_testL (m + 2) v)).card = 2 * k := by
    have : (Finset.univ.filter (fun (v : Fin (m + 2)) => (0 : Fin 3) ∈ cycle_not_prop_testL (m + 2) v)) = Finset.univ := by
      ext v
      simp only [mem_filter, mem_univ, true_and]
      dsimp [cycle_not_prop_testL]
      split_ifs <;> decide
    rw [this, card_univ, Fintype.card_fin, hk]
  have huses0 := hf_uses 0
  dsimp only at huses0
  rw [hη0] at huses0
  have hS_card : S.card = k := by
    change (Finset.univ.filter (fun (v : Fin (m + 2)) => f v = 0)).card = k
    rw [Nat.ceilDiv_eq_add_pred_div] at huses0
    omega
  have hcompl_card : Sᶜ.card = k := by
    rw [card_compl, Fintype.card_fin, hS_card]
    omega
  have h_disj : ∀ u ∈ S, u + 1 ∉ S := by
    intro u hu hu1
    rw [hmem_S] at hu hu1
    have hadj := cycle_not_prop_cycle_adj_succ m u
    have hne := f.valid hadj
    rw [hu, hu1] at hne
    exact hne rfl
  have h_shift := cycle_not_prop_shift_iff m S k hS_card hcompl_card h_disj
  have h_fin := cycle_not_prop_fin_mem_S_iff m S h_shift
  have h_cases : (∀ v, f v = 0 ↔ v.val % 2 = 0) ∨ (∀ v, f v = 0 ↔ v.val % 2 ≠ 0) := by
    by_cases h0 : f 0 = 0
    · left
      intro v
      have hv := h_fin v
      rw [hmem_S, hmem_S] at hv
      tauto
    · right
      intro v
      have hv := h_fin v
      rw [hmem_S, hmem_S] at hv
      tauto
  have hη1 : (Finset.univ.filter (fun (v : Fin (m + 2)) => (1 : Fin 3) ∈ cycle_not_prop_testL (m + 2) v)).card = k := by
    have : (Finset.univ.filter (fun (v : Fin (m + 2)) => (1 : Fin 3) ∈ cycle_not_prop_testL (m + 2) v)) =
        (Finset.univ.filter (fun (v : Fin (m + 2)) => v.val % 2 = 0)) := by
      ext v
      simp only [mem_filter, mem_univ, true_and]
      dsimp [cycle_not_prop_testL]
      split_ifs with h <;> simp [h]
    rw [this, cycle_not_prop_card_even m k hk]
  have hη2 : (Finset.univ.filter (fun (v : Fin (m + 2)) => (2 : Fin 3) ∈ cycle_not_prop_testL (m + 2) v)).card = k := by
    have : (Finset.univ.filter (fun (v : Fin (m + 2)) => (2 : Fin 3) ∈ cycle_not_prop_testL (m + 2) v)) =
        (Finset.univ.filter (fun (v : Fin (m + 2)) => v.val % 2 ≠ 0)) := by
      ext v
      simp only [mem_filter, mem_univ, true_and]
      dsimp [cycle_not_prop_testL]
      split_ifs with h <;> simp [h]
    rw [this, cycle_not_prop_card_odd m k hk]
  rcases h_cases with h_even | h_odd
  · have huses1 := hf_uses 1
    dsimp only at huses1
    rw [hη1] at huses1
    have h1_ge : 1 ≤ (Finset.univ.filter (fun v => f v = 1)).card := by
      rw [Nat.ceilDiv_eq_add_pred_div] at huses1
      omega
    have h1_zero : (Finset.univ.filter (fun v => f v = 1)).card = 0 := by
      have : (Finset.univ.filter (fun v => f v = 1)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v _
        by_cases hv : v.val % 2 = 0
        · have h0 : f v = 0 := (h_even v).2 hv
          intro h1
          have : (0 : Fin 3) = 1 := h0.symm.trans h1
          revert this; decide
        · have hL : f v ∈ cycle_not_prop_testL (m + 2) v := hf_list v
          dsimp [cycle_not_prop_testL] at hL
          rw [if_neg hv] at hL
          intro h1
          rw [h1] at hL
          revert hL; decide
      rw [this, card_empty]
    omega
  · have huses2 := hf_uses 2
    dsimp only at huses2
    rw [hη2] at huses2
    have h2_ge : 1 ≤ (Finset.univ.filter (fun v => f v = 2)).card := by
      rw [Nat.ceilDiv_eq_add_pred_div] at huses2
      omega
    have h2_zero : (Finset.univ.filter (fun v => f v = 2)).card = 0 := by
      have : (Finset.univ.filter (fun v => f v = 2)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro v _
        by_cases hv : v.val % 2 = 0
        · have hL : f v ∈ cycle_not_prop_testL (m + 2) v := hf_list v
          dsimp [cycle_not_prop_testL] at hL
          rw [if_pos hv] at hL
          intro h2
          rw [h2] at hL
          revert hL; decide
        · have h0 : f v = 0 := (h_odd v).2 hv
          intro h2
          have : (0 : Fin 3) = 2 := h0.symm.trans h2
          revert this; decide
      rw [this, card_empty]
    omega
