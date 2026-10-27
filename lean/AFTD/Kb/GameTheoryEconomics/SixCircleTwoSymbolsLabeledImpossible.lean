import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SixCircleView

/-!
# six_circle_two_symbols_labeled_impossible

Topic: combinatorial_games   Node: 69535e10cfa8

Provenance: formalization of a published result. Source: arXiv:2610.33032, Theorem 8

In the anonymous-slip puzzle for six sages seated in a circle with six labeled seats, there is no deterministic protocol c : (Fin 6 × Fin 6 × Fin 6 × Fin 6) → Fin 2 using two symbols {0, 1} such that every sage can reconstruct the full seating permutation from their local view and the public multiset of written symbols: that is, there is no protocol c such that for all permutations π₁, π₂ of six sages and every seat i, if the local views (π₁ i, i, π₁ (i - 1), π₁ (i + 1)) and (π₂ i, i, π₂ (i - 1), π₂ (i + 1)) are equal and the total number of 1s written under c is equal, then π₁ = π₂.
-/

open BigOperators

def six_circle_two_symbols_labeled_impossible_total (c : (Fin 6 × Fin 6 × Fin 6 × Fin 6) → Fin 2) (π : Equiv.Perm (Fin 6)) : ℕ :=
  ∑ j : Fin 6, (c (six_circle_view π j) : ℕ)

lemma six_circle_two_symbols_labeled_impossible_card_filter_eq_one_of_injOn_of_mem_image
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset α} {f : α → β} {k : β}
    (hinj : Set.InjOn f s) (hk : k ∈ s.image f) :
    (s.filter (fun x => f x = k)).card = 1 := by
  rcases Finset.mem_image.mp hk with ⟨x, hx, rfl⟩
  have : s.filter (fun y => f y = f x) = {x} := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hy, heq⟩
      exact hinj hy hx heq
    · rintro rfl
      exact ⟨hx, rfl⟩
  rw [this, Finset.card_singleton]

lemma six_circle_two_symbols_labeled_impossible_view_eq_iff (π π₀ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    six_circle_view π i = six_circle_view π₀ i ↔
      π i = π₀ i ∧ π (i - 1) = π₀ (i - 1) ∧ π (i + 1) = π₀ (i + 1) := by
  simp [six_circle_view]

lemma six_circle_two_symbols_labeled_impossible_card_fiber_view (π₀ : Equiv.Perm (Fin 6)) (i : Fin 6) :
    (Finset.filter (fun π => six_circle_view π i = six_circle_view π₀ i) Finset.univ).card = 6 := by
  have h_stab : (Finset.filter (fun (σ : Equiv.Perm (Fin 6)) =>
      σ i = i ∧ σ (i - 1) = i - 1 ∧ σ (i + 1) = i + 1) Finset.univ).card = 6 := by
    revert i; decide
  have h_bij : (Finset.filter (fun π => six_circle_view π i = six_circle_view π₀ i) Finset.univ).card =
      (Finset.filter (fun (σ : Equiv.Perm (Fin 6)) =>
        σ i = i ∧ σ (i - 1) = i - 1 ∧ σ (i + 1) = i + 1) Finset.univ).card := by
    apply Finset.card_bij' (fun π _ => π₀⁻¹ * π) (fun σ _ => π₀ * σ)
    · intro π hπ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hπ ⊢
      rw [six_circle_two_symbols_labeled_impossible_view_eq_iff] at hπ
      refine ⟨?_, ?_, ?_⟩
      · simp [Equiv.Perm.mul_apply, hπ.1]
      · simp [Equiv.Perm.mul_apply, hπ.2.1]
      · simp [Equiv.Perm.mul_apply, hπ.2.2]
    · intro σ hσ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
      rw [six_circle_two_symbols_labeled_impossible_view_eq_iff]
      refine ⟨?_, ?_, ?_⟩
      · simp [Equiv.Perm.mul_apply, hσ.1]
      · simp [Equiv.Perm.mul_apply, hσ.2.1]
      · simp [Equiv.Perm.mul_apply, hσ.2.2]
    · intro π _; simp
    · intro σ _; simp
  rw [h_bij, h_stab]

lemma six_circle_two_symbols_labeled_impossible_total_eq_add (c : (Fin 6 × Fin 6 × Fin 6 × Fin 6) → Fin 2) (π : Equiv.Perm (Fin 6)) (i : Fin 6) :
    six_circle_two_symbols_labeled_impossible_total c π = (c (six_circle_view π i) : ℕ) + ∑ j ∈ Finset.univ.erase i, (c (six_circle_view π j) : ℕ) := by
  dsimp [six_circle_two_symbols_labeled_impossible_total]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]

lemma six_circle_two_symbols_labeled_impossible_sum_erase_le_five (c : (Fin 6 × Fin 6 × Fin 6 × Fin 6) → Fin 2) (π : Equiv.Perm (Fin 6)) (i : Fin 6) :
    ∑ j ∈ Finset.univ.erase i, (c (six_circle_view π j) : ℕ) ≤ 5 := by
  have h_le : ∀ j ∈ Finset.univ.erase i, (c (six_circle_view π j) : ℕ) ≤ 1 := by
    intro j _
    obtain ⟨v, hv⟩ := c (six_circle_view π j)
    omega
  have h_sum := Finset.sum_le_card_nsmul (Finset.univ.erase i) (fun j => (c (six_circle_view π j) : ℕ)) 1 h_le
  have h_card : (Finset.univ.erase i).card = 5 := by simp
  rw [h_card] at h_sum
  simpa using h_sum

lemma six_circle_two_symbols_labeled_impossible_card_filter_fiber_eq_one
    (c : (Fin 6 × Fin 6 × Fin 6 × Fin 6) → Fin 2)
    (h : ∀ (π₁ π₂ : Equiv.Perm (Fin 6)) (i : Fin 6),
      six_circle_view π₁ i = six_circle_view π₂ i →
        six_circle_two_symbols_labeled_impossible_total c π₁ = six_circle_two_symbols_labeled_impossible_total c π₂ → π₁ = π₂)
    (π₀ : Equiv.Perm (Fin 6)) (i : Fin 6) (k : ℕ) (hk : k = 1 ∨ k = 2) :
    (Finset.filter (fun π => six_circle_view π i = six_circle_view π₀ i ∧
      six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ).card = 1 := by
  let s := Finset.filter (fun π => six_circle_view π i = six_circle_view π₀ i) Finset.univ
  have hs_card : s.card = 6 := six_circle_two_symbols_labeled_impossible_card_fiber_view π₀ i
  have hinj : Set.InjOn (six_circle_two_symbols_labeled_impossible_total c) (s : Set (Equiv.Perm (Fin 6))) := by
    intro π₁ h1 π₂ h2 htot
    simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
    exact h π₁ π₂ i (h1.trans h2.symm) htot
  have h_img_card : (s.image (six_circle_two_symbols_labeled_impossible_total c)).card = 6 := by
    rw [Finset.card_image_of_injOn hinj, hs_card]
  let b := (c (six_circle_view π₀ i) : ℕ)
  have hb_le : b ≤ 1 := by
    obtain ⟨bv, hbv⟩ := c (six_circle_view π₀ i)
    omega
  have h_sub : s.image (six_circle_two_symbols_labeled_impossible_total c) ⊆ Finset.Icc b (b + 5) := by
    intro t ht
    rcases Finset.mem_image.mp ht with ⟨π, hπ, rfl⟩
    simp only [s, Finset.mem_filter, Finset.mem_univ, true_and] at hπ
    simp only [Finset.mem_Icc]
    rw [six_circle_two_symbols_labeled_impossible_total_eq_add c π i, hπ]
    refine ⟨by omega, ?_⟩
    have := six_circle_two_symbols_labeled_impossible_sum_erase_le_five c π i
    omega
  have h_icc_card : (Finset.Icc b (b + 5)).card = 6 := by
    simp; omega
  have h_img_eq : s.image (six_circle_two_symbols_labeled_impossible_total c) = Finset.Icc b (b + 5) :=
    Finset.eq_of_subset_of_card_le h_sub (by rw [h_img_card, h_icc_card])
  have hk_in : k ∈ s.image (six_circle_two_symbols_labeled_impossible_total c) := by
    rw [h_img_eq, Finset.mem_Icc]
    rcases hk with rfl | rfl <;> omega
  have hk_card := six_circle_two_symbols_labeled_impossible_card_filter_eq_one_of_injOn_of_mem_image hinj hk_in
  have h_eq : (Finset.filter (fun π => six_circle_view π i = six_circle_view π₀ i ∧
      six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ) =
      s.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = k) := by
    ext π; simp [s, and_comm]
  rw [h_eq, hk_card]

lemma six_circle_two_symbols_labeled_impossible_card_filter_fiber_eq
    (c : (Fin 6 × Fin 6 × Fin 6 × Fin 6) → Fin 2)
    (h : ∀ (π₁ π₂ : Equiv.Perm (Fin 6)) (i : Fin 6),
      six_circle_view π₁ i = six_circle_view π₂ i →
        six_circle_two_symbols_labeled_impossible_total c π₁ = six_circle_two_symbols_labeled_impossible_total c π₂ → π₁ = π₂)
    (i : Fin 6) (v : Fin 6 × Fin 6 × Fin 6 × Fin 6) :
    (Finset.filter (fun π => six_circle_view π i = v ∧ six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ).card =
    (Finset.filter (fun π => six_circle_view π i = v ∧ six_circle_two_symbols_labeled_impossible_total c π = 2) Finset.univ).card := by
  by_cases hne : ∃ π₀, six_circle_view π₀ i = v
  · rcases hne with ⟨π₀, rfl⟩
    rw [six_circle_two_symbols_labeled_impossible_card_filter_fiber_eq_one c h π₀ i 1 (Or.inl rfl),
        six_circle_two_symbols_labeled_impossible_card_filter_fiber_eq_one c h π₀ i 2 (Or.inr rfl)]
  · have h1 : (Finset.filter (fun π => six_circle_view π i = v ∧ six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ) = ∅ := by
      ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hvi, _⟩
      exact hne ⟨π, hvi⟩
    have h2 : (Finset.filter (fun π => six_circle_view π i = v ∧ six_circle_two_symbols_labeled_impossible_total c π = 2) Finset.univ) = ∅ := by
      ext π
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      rintro ⟨hvi, _⟩
      exact hne ⟨π, hvi⟩
    rw [h1, h2]

lemma six_circle_two_symbols_labeled_impossible_card_total_fiberwise
    (c : (Fin 6 × Fin 6 × Fin 6 × Fin 6) → Fin 2) (k : ℕ) (i : Fin 6) :
    (Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ).card =
    ∑ v : Fin 6 × Fin 6 × Fin 6 × Fin 6,
      (Finset.filter (fun π => six_circle_view π i = v ∧ six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ).card := by
  let s := Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ
  rw [Finset.card_eq_sum_ones, ← Finset.sum_fiberwise s (fun π => six_circle_view π i) (fun _ => 1)]
  apply Finset.sum_congr rfl
  intro v _
  have h_sub : (Finset.filter (fun π => six_circle_view π i = v) s).card =
      (Finset.filter (fun π => six_circle_view π i = v ∧ six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ).card := by
    congr 1; ext π; simp [s, and_comm]
  rw [Finset.sum_const, smul_eq_mul, mul_one, h_sub]

lemma six_circle_two_symbols_labeled_impossible_sum_view_fiberwise
    (c : (Fin 6 × Fin 6 × Fin 6 × Fin 6) → Fin 2) (k : ℕ) (i : Fin 6) :
    ∑ π ∈ Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ, (c (six_circle_view π i) : ℕ) =
    ∑ v : Fin 6 × Fin 6 × Fin 6 × Fin 6,
      (Finset.filter (fun π => six_circle_view π i = v ∧ six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ).card * (c v : ℕ) := by
  let s := Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ
  rw [← Finset.sum_fiberwise s (fun π => six_circle_view π i) (fun π => (c (six_circle_view π i) : ℕ))]
  apply Finset.sum_congr rfl
  intro v _
  have h_congr : ∀ π ∈ Finset.filter (fun π => six_circle_view π i = v) s,
      (c (six_circle_view π i) : ℕ) = (c v : ℕ) := by
    intro π hπ
    simp only [s, Finset.mem_filter] at hπ
    rw [hπ.2]
  have h_sub : (Finset.filter (fun π => six_circle_view π i = v) s).card =
      (Finset.filter (fun π => six_circle_view π i = v ∧ six_circle_two_symbols_labeled_impossible_total c π = k) Finset.univ).card := by
    congr 1; ext π; simp [s, and_comm]
  rw [Finset.sum_congr rfl h_congr, Finset.sum_const, nsmul_eq_mul, h_sub]
  rfl

/-- Theorem 8 (arXiv:2610.33032): The 6C2L anonymous-slip puzzle has no deterministic solution. -/
theorem six_circle_two_symbols_labeled_impossible :
    ¬ ∃ c : (Fin 6 × Fin 6 × Fin 6 × Fin 6) → Fin 2,
      ∀ (π₁ π₂ : Equiv.Perm (Fin 6)) (i : Fin 6),
        (π₁ i, i, π₁ (i - 1), π₁ (i + 1)) = (π₂ i, i, π₂ (i - 1), π₂ (i + 1)) →
        (∑ j : Fin 6, (c (π₁ j, j, π₁ (j - 1), π₁ (j + 1)) : ℕ)) =
          (∑ j : Fin 6, (c (π₂ j, j, π₂ (j - 1), π₂ (j + 1)) : ℕ)) →
        π₁ = π₂ := by
  rintro ⟨c, hc⟩
  have h : ∀ (π₁ π₂ : Equiv.Perm (Fin 6)) (i : Fin 6),
      six_circle_view π₁ i = six_circle_view π₂ i →
        six_circle_two_symbols_labeled_impossible_total c π₁ = six_circle_two_symbols_labeled_impossible_total c π₂ → π₁ = π₂ := by
    intro π₁ π₂ i hview htot
    exact hc π₁ π₂ i hview htot
  have h_card_eq : (Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ).card =
      (Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 2) Finset.univ).card := by
    rw [six_circle_two_symbols_labeled_impossible_card_total_fiberwise c 1 0,
        six_circle_two_symbols_labeled_impossible_card_total_fiberwise c 2 0]
    apply Finset.sum_congr rfl
    intro v _
    exact six_circle_two_symbols_labeled_impossible_card_filter_fiber_eq c h 0 v
  have h_view_eq : ∀ i : Fin 6,
      ∑ π ∈ Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ, (c (six_circle_view π i) : ℕ) =
      ∑ π ∈ Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 2) Finset.univ, (c (six_circle_view π i) : ℕ) := by
    intro i
    rw [six_circle_two_symbols_labeled_impossible_sum_view_fiberwise c 1 i,
        six_circle_two_symbols_labeled_impossible_sum_view_fiberwise c 2 i]
    apply Finset.sum_congr rfl
    intro v _
    rw [six_circle_two_symbols_labeled_impossible_card_filter_fiber_eq c h i v]
  have h_sum_all :
      ∑ i : Fin 6, ∑ π ∈ Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ, (c (six_circle_view π i) : ℕ) =
      ∑ i : Fin 6, ∑ π ∈ Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 2) Finset.univ, (c (six_circle_view π i) : ℕ) := by
    apply Finset.sum_congr rfl
    intro i _
    exact h_view_eq i
  rw [Finset.sum_comm] at h_sum_all
  rw [Finset.sum_comm (s := Finset.univ)] at h_sum_all
  have h1 : (∑ x ∈ Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ,
        ∑ y : Fin 6, (c (six_circle_view x y) : ℕ)) =
      (Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ).card := by
    have : ∀ x ∈ Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ,
        (∑ y : Fin 6, (c (six_circle_view x y) : ℕ)) = 1 := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      exact hx.2
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one]
    rfl
  have h2 : (∑ x ∈ Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 2) Finset.univ,
        ∑ y : Fin 6, (c (six_circle_view x y) : ℕ)) =
      2 * (Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 2) Finset.univ).card := by
    have : ∀ x ∈ Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 2) Finset.univ,
        (∑ y : Fin 6, (c (six_circle_view x y) : ℕ)) = 2 := by
      intro x hx
      simp only [Finset.mem_filter] at hx
      exact hx.2
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_comm]
    rfl
  rw [h1, h2] at h_sum_all
  have h_pos : 0 < (Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ).card := by
    have h_sub : (Finset.filter (fun π => six_circle_view π 0 = six_circle_view 1 0 ∧
        six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ) ⊆
        Finset.filter (fun π => six_circle_two_symbols_labeled_impossible_total c π = 1) Finset.univ := by
      intro π hπ
      simp only [Finset.mem_filter] at hπ ⊢
      exact ⟨hπ.1, hπ.2.2⟩
    have h_le := Finset.card_le_card h_sub
    have h_one := six_circle_two_symbols_labeled_impossible_card_filter_fiber_eq_one c h 1 0 1 (Or.inl rfl)
    omega
  omega
