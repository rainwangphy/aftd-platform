import AFTD.Prelude
import AFTD.Kb.Tcs.HammingCloseSkewSystem

/-!
# op_1859_close_skew_r_eq_two

Topic: combinatorics   Node: 021f2f88c5fd

Provenance: formalization of a published result. Source: arXiv:2611.20820 Sec. 5.7, Theorem 4.3

Let n > 2 be a natural number. If v and w are sequences of k points in {0,1}^n forming a close-skew system of radius 2, then k <= 4.
-/

open Finset

private def op1859_diffSet {n : ℕ} (x y : Fin n → Bool) : Finset (Fin n) :=
  Finset.filter (fun i => x i ≠ y i) Finset.univ

private theorem op1859_mem_diffSet {n : ℕ} (x y : Fin n → Bool) (i : Fin n) :
    i ∈ op1859_diffSet x y ↔ x i ≠ y i := by
  simp [op1859_diffSet]

private theorem op1859_symmDiff_diffSet {n : ℕ} (x y z : Fin n → Bool) :
    symmDiff (op1859_diffSet x z) (op1859_diffSet y z) = op1859_diffSet x y := by
  ext i
  simp only [Finset.mem_symmDiff, op1859_mem_diffSet]
  cases x i <;> cases y i <;> cases z i <;> decide

private theorem op1859_diffSet_card_comm {n : ℕ} (x y : Fin n → Bool) :
    (op1859_diffSet x y).card = (op1859_diffSet y x).card := by
  congr 1
  ext i
  simp only [op1859_mem_diffSet]
  exact ne_comm

private theorem op1859_card_symmDiff_add_card {α : Type*} [DecidableEq α] (A D : Finset α) :
    (symmDiff A D).card + A.card = D.card + 2 * (A \ D).card := by
  have hsymm : (symmDiff A D).card = (A \ D).card + (D \ A).card := by
    change ((A \ D) ∪ (D \ A)).card = (A \ D).card + (D \ A).card
    exact card_union_of_disjoint disjoint_sdiff_sdiff
  have hA := card_inter_add_card_sdiff A D
  have hD := card_inter_add_card_sdiff D A
  rw [inter_comm] at hD
  omega

private theorem op1859_subset_of_symmDiff_le_two {α : Type*} [DecidableEq α] {A D : Finset α}
    (hAD : (symmDiff A D).card ≤ 2) (hA : A.card ≤ 2) (hD : 3 ≤ D.card) :
    A ⊆ D ∧ D.card ≤ 4 ∧ (D.card - 2 ≤ A.card) := by
  have h := op1859_card_symmDiff_add_card A D
  have h_le : D.card + 2 * (A \ D).card ≤ 4 := by omega
  have h_sdiff : (A \ D).card = 0 := by omega
  have h_sub : A ⊆ D := by
    rw [← sdiff_eq_empty_iff_subset]
    exact card_eq_zero.mp h_sdiff
  have hD4 : D.card ≤ 4 := by omega
  have hA_ge : D.card - 2 ≤ A.card := by
    have hD_sub : (D \ A).card = D.card - A.card := by
      rw [card_sdiff_of_subset h_sub]
    have hsymm : (symmDiff A D).card = (D \ A).card := by
      have h1 : (symmDiff A D).card = (A \ D).card + (D \ A).card := by
        change ((A \ D) ∪ (D \ A)).card = (A \ D).card + (D \ A).card
        exact card_union_of_disjoint disjoint_sdiff_sdiff
      omega
    omega
  exact ⟨h_sub, hD4, hA_ge⟩

private theorem op1859_diffSet_inj {n : ℕ} (x y z : Fin n → Bool)
    (h : op1859_diffSet x z = op1859_diffSet y z) : x = y := by
  ext i
  have : i ∈ op1859_diffSet x z ↔ i ∈ op1859_diffSet y z := by rw [h]
  simp only [op1859_diffSet, Finset.mem_filter, Finset.mem_univ, true_and] at this
  cases h1 : x i <;> cases h2 : y i <;> cases h3 : z i <;> simp_all

private theorem op1859_sdiff_singleton_inj {α : Type*} [DecidableEq α] {T1 T2 : Finset α} {e : α}
    (he1 : e ∈ T1) (he2 : e ∈ T2) (h : T1 \ {e} = T2 \ {e}) : T1 = T2 := by
  ext x
  by_cases hx : x = e
  · subst hx; simp [he1, he2]
  · have hx1 : x ∈ T1 ↔ x ∈ T1 \ {e} := by simp [hx]
    have hx2 : x ∈ T2 ↔ x ∈ T2 \ {e} := by simp [hx]
    rw [hx1, hx2, h]

private theorem op1859_f_inj_on {α : Type*} [DecidableEq α] {D : Finset α} {e : α}
    {A B : Finset α} (hA : A ⊆ D) (hB : B ⊆ D)
    (hdist : (symmDiff A B).card ≤ 2) (hD3 : 3 ≤ D.card)
    (hf : (if e ∈ A then A else D \ A) = (if e ∈ B then B else D \ B)) :
    A = B := by
  split_ifs at hf with h1 h2
  · exact hf
  · exfalso
    have hAB : A = D \ B := hf
    have hsymm : symmDiff A B = D := by
      rw [hAB]
      change ((D \ B) \ B) ∪ (B \ (D \ B)) = D
      ext x
      simp only [mem_union, mem_sdiff]
      constructor
      · rintro (⟨⟨hxD, _⟩, _⟩ | ⟨hxB, _⟩)
        · exact hxD
        · exact hB hxB
      · intro hxD
        by_cases hxB : x ∈ B
        · right
          refine ⟨hxB, ?_⟩
          simp [hxD, hxB]
        · left
          exact ⟨⟨hxD, hxB⟩, hxB⟩
    have : (symmDiff A B).card = D.card := by rw [hsymm]
    omega
  · exfalso
    have hAB : D \ A = B := hf
    have hsymm : symmDiff A B = D := by
      rw [← hAB]
      change (A \ (D \ A)) ∪ ((D \ A) \ A) = D
      ext x
      simp only [mem_union, mem_sdiff]
      constructor
      · rintro (⟨hxA, _⟩ | ⟨⟨hxD, _⟩, _⟩)
        · exact hA hxA
        · exact hxD
      · intro hxD
        by_cases hxA : x ∈ A
        · left
          refine ⟨hxA, ?_⟩
          simp [hxD, hxA]
        · right
          exact ⟨⟨hxD, hxA⟩, hxA⟩
    have : (symmDiff A B).card = D.card := by rw [hsymm]
    omega
  · have : D \ (D \ A) = D \ (D \ B) := by rw [hf]
    rw [Finset.sdiff_sdiff_eq_self hA, Finset.sdiff_sdiff_eq_self hB] at this
    exact this

private theorem op1859_pigeonhole_four_three {α : Type*} [DecidableEq α]
    (f : Fin 4 → α) (s : Finset α) (hs : s.card ≤ 3) (hf : ∀ i, f i ∈ s) :
    ∃ i j : Fin 4, i ≠ j ∧ f i = f j := by
  by_contra! h_inj
  have h_card : (univ.image f).card = 4 := by
    rw [card_image_of_injective _]
    · rfl
    · intro i j hij
      by_contra hne
      exact h_inj i j hne hij
  have h_sub : univ.image f ⊆ s := by
    intro x hx
    rcases mem_image.mp hx with ⟨i, _, rfl⟩
    exact hf i
  have := card_le_card h_sub
  omega

private theorem op1859_card_four_case {α : Type*} [DecidableEq α] {D : Finset α} {e : α}
    (he : e ∈ D) (hD : D.card = 4)
    {A : Finset α} (hA : A ⊆ D) (hA_le : A.card ≤ 2) (hA_ge : 4 - 2 ≤ A.card) :
    let T := if e ∈ A then A else D \ A
    (T \ {e}) ∈ powersetCard 1 (D \ {e}) := by
  intro T
  have hAc : A.card = 2 := by omega
  have hTe : e ∈ T := by
    dsimp [T]
    split_ifs with h1
    · exact h1
    · rw [mem_sdiff]; exact ⟨he, h1⟩
  have hT_sub : T ⊆ D := by
    dsimp [T]
    split_ifs <;> [exact hA; exact sdiff_subset]
  have hTc : T.card = 2 := by
    dsimp [T]
    split_ifs
    · exact hAc
    · rw [card_sdiff_of_subset hA, hD, hAc]
  rw [mem_powersetCard]
  refine ⟨sdiff_subset_sdiff hT_sub (subset_refl _), ?_⟩
  rw [card_sdiff_of_subset (singleton_subset_iff.mpr hTe), card_singleton, hTc]

private theorem op1859_card_three_case {α : Type*} [DecidableEq α] {D : Finset α} {e : α}
    (he : e ∈ D) (hD : D.card = 3)
    {A : Finset α} (hA : A ⊆ D) (hA_le : A.card ≤ 2) (hA_ge : 3 - 2 ≤ A.card) :
    let T := if e ∈ A then A else D \ A
    (T \ {e}) ∈ powersetCard 0 (D \ {e}) ∪ powersetCard 1 (D \ {e}) := by
  intro T
  have hTe : e ∈ T := by
    dsimp [T]
    split_ifs with h1
    · exact h1
    · rw [mem_sdiff]; exact ⟨he, h1⟩
  have hT_sub : T ⊆ D := by
    dsimp [T]
    split_ifs <;> [exact hA; exact sdiff_subset]
  have hTc : 1 ≤ T.card ∧ T.card ≤ 2 := by
    dsimp [T]
    split_ifs
    · omega
    · rw [card_sdiff_of_subset hA, hD]
      omega
  have hS_card : (T \ {e}).card = T.card - 1 := by
    rw [card_sdiff_of_subset (singleton_subset_iff.mpr hTe), card_singleton]
  have hS_sub : T \ {e} ⊆ D \ {e} := sdiff_subset_sdiff hT_sub (subset_refl _)
  rw [mem_union, mem_powersetCard, mem_powersetCard]
  have : (T \ {e}).card = 0 ∨ (T \ {e}).card = 1 := by omega
  rcases this with h | h
  · left; exact ⟨hS_sub, h⟩
  · right; exact ⟨hS_sub, h⟩

/-- The close-skew set-pair bound holds for radius r = 2. -/
theorem op_1859_close_skew_r_eq_two {n k : ℕ} (hn : 2 < n)
    (v w : Fin k → Fin n → Bool) (h : hamming_close_skew_system 2 v w) :
    k ≤ 4 := by
  by_contra! hk
  have hi : ∀ (m : ℕ), m < 5 → m < k := fun m _ => by omega
  let idx : Fin 5 → Fin k := fun m => ⟨m.val, hi m.val m.isLt⟩
  rcases h with ⟨hclose, hfar, hskew⟩
  let a := v (idx 4)
  let b := w (idx 4)
  let D := op1859_diffSet b a
  have hD3 : 3 ≤ D.card := by
    have := hfar (idx 4)
    exact this
  let S : Fin 4 → Finset (Fin n) := fun m => op1859_diffSet (v (idx ⟨m.val, by omega⟩)) a
  have hS_prop : ∀ m : Fin 4, S m ⊆ D ∧ D.card ≤ 4 ∧ (D.card - 2 ≤ (S m).card) ∧ (S m).card ≤ 2 := by
    intro m
    have hm4 : (idx ⟨m.val, by omega⟩) < idx 4 := by
      show m.val < 4
      exact m.isLt
    have hclose_m : (S m).card ≤ 2 := hclose (idx ⟨m.val, by omega⟩) (idx 4)
    have hsymm_m : (symmDiff (S m) D).card ≤ 2 := by
      rw [op1859_symmDiff_diffSet]
      have := hskew (idx 4) (idx ⟨m.val, by omega⟩) hm4
      rw [op1859_diffSet_card_comm]
      exact this
    have ⟨hsub, hD4, hge⟩ := op1859_subset_of_symmDiff_le_two hsymm_m hclose_m hD3
    exact ⟨hsub, hD4, hge, hclose_m⟩
  have hD_nonempty : D.Nonempty := by
    by_contra h_emp
    have : D = ∅ := not_nonempty_iff_eq_empty.mp h_emp
    rw [this] at hD3
    contradiction
  rcases hD_nonempty with ⟨e, he⟩
  have hD_cases : D.card = 3 ∨ D.card = 4 := by
    have hD4 := (hS_prop 0).2.1
    omega
  have hdist : ∀ j m : Fin 4, (symmDiff (S j) (S m)).card ≤ 2 := by
    intro j m
    rw [op1859_symmDiff_diffSet]
    exact hclose (idx ⟨j.val, by omega⟩) (idx ⟨m.val, by omega⟩)
  have hS_inj : ∀ j m : Fin 4, j ≠ m → S j ≠ S m := by
    intro j m hjm heq
    have hv_eq := op1859_diffSet_inj (v (idx ⟨j.val, by omega⟩)) (v (idx ⟨m.val, by omega⟩)) a heq
    wlog hj_lt_m : j < m generalizing j m
    · have hmj : m < j := by omega
      exact this m j hjm.symm heq.symm hv_eq.symm hmj
    have hlt : idx ⟨j.val, by omega⟩ < idx ⟨m.val, by omega⟩ := by
      show j.val < m.val
      exact hj_lt_m
    have hfar_m := hfar (idx ⟨m.val, by omega⟩)
    have hskew_jm := hskew (idx ⟨m.val, by omega⟩) (idx ⟨j.val, by omega⟩) hlt
    rw [hv_eq] at hskew_jm
    omega
  let T : Fin 4 → Finset (Fin n) := fun m => if e ∈ S m then S m else D \ S m
  have hTe : ∀ m, e ∈ T m := by
    intro m
    dsimp [T]
    split_ifs with h1
    · exact h1
    · rw [mem_sdiff]; exact ⟨he, h1⟩
  let g : Fin 4 → Finset (Fin n) := fun m => T m \ {e}
  have hg_inj : ∀ j m : Fin 4, g j = g m → j = m := by
    intro j m hg
    have hT_eq : T j = T m := op1859_sdiff_singleton_inj (hTe j) (hTe m) hg
    have hS_eq : S j = S m := op1859_f_inj_on (hS_prop j).1 (hS_prop m).1 (hdist j m) hD3 hT_eq
    by_contra hjm
    exact hS_inj j m hjm hS_eq
  rcases hD_cases with hD3_eq | hD4_eq
  · let s := powersetCard 0 (D \ {e}) ∪ powersetCard 1 (D \ {e})
    have hs_card : s.card ≤ 3 := by
      have hDe : (D \ {e}).card = 2 := by
        rw [card_sdiff_of_subset (singleton_subset_iff.mpr he), card_singleton, hD3_eq]
      have hdisj : Disjoint (powersetCard 0 (D \ {e})) (powersetCard 1 (D \ {e})) := by
        have := pairwise_disjoint_powersetCard (D \ {e})
        exact this (by decide)
      rw [card_union_of_disjoint hdisj, card_powersetCard, card_powersetCard,
          Nat.choose_zero_right, Nat.choose_one_right, hDe]
    have hg_mem : ∀ m, g m ∈ s := by
      intro m
      have hge : 3 - 2 ≤ (S m).card := by
        have := (hS_prop m).2.2.1
        omega
      exact op1859_card_three_case he hD3_eq (hS_prop m).1 (hS_prop m).2.2.2 hge
    rcases op1859_pigeonhole_four_three g s hs_card hg_mem with ⟨j, m, hjm, hg_eq⟩
    exact hjm (hg_inj j m hg_eq)
  · let s := powersetCard 1 (D \ {e})
    have hs_card : s.card ≤ 3 := by
      have hDe : (D \ {e}).card = 3 := by
        rw [card_sdiff_of_subset (singleton_subset_iff.mpr he), card_singleton, hD4_eq]
      rw [card_powersetCard, Nat.choose_one_right, hDe]
    have hg_mem : ∀ m, g m ∈ s := by
      intro m
      have hge : 4 - 2 ≤ (S m).card := by
        have := (hS_prop m).2.2.1
        omega
      exact op1859_card_four_case he hD4_eq (hS_prop m).1 (hS_prop m).2.2.2 hge
    rcases op1859_pigeonhole_four_three g s hs_card hg_mem with ⟨j, m, hjm, hg_eq⟩
    exact hjm (hg_inj j m hg_eq)
