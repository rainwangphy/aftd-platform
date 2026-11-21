import AFTD.Prelude

/-!
# ghz_separating_functional_matrix

Topic: quantum   Node: 3d2af10d4a54

Provenance: formalization of a published result. Source: arXiv:2611.26300 Lemma (The (N-1) x N lemma)

Let N ≥ 4 and let A be an (N - 1) × N complex matrix. There exists a family of vectors v : Fin (N - 1) → Fin N → ℂ such that for every row r : Fin (N - 1), ∑ j : Fin N, A r j * v r j = 0, but ∑ j : Fin N, ∏ r : Fin (N - 1), v r j ≠ 0.
-/

open BigOperators

noncomputable def ghz_separating_functional_matrix_make_v_row {N : ℕ} (A_r : Fin N → ℂ) (j_star : Fin N) (q : Fin N) : Fin N → ℂ :=
  if A_r j_star = 0 then
    fun j => if j = j_star then 1 else 0
  else
    fun j => if j = j_star then A_r q else if j = q then - A_r j_star else 0

lemma ghz_separating_functional_matrix_make_v_row_dot_zero {N : ℕ} (A_r : Fin N → ℂ) (j_star : Fin N) (q : Fin N)
    (hq_ne : A_r j_star ≠ 0 → q ≠ j_star) :
    ∑ j : Fin N, A_r j * ghz_separating_functional_matrix_make_v_row A_r j_star q j = 0 := by
  classical
  dsimp [ghz_separating_functional_matrix_make_v_row]
  split_ifs with h0
  · rw [Fintype.sum_eq_single j_star]
    · simp [h0]
    · intro j hj; simp [hj]
  · have hq_ne' := hq_ne h0
    have h_sub : ({j_star, q} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
    have h_eq : (∑ j : Fin N, A_r j * (if j = j_star then A_r q else if j = q then - A_r j_star else 0)) =
        ∑ j ∈ ({j_star, q} : Finset (Fin N)), A_r j * (if j = j_star then A_r q else if j = q then - A_r j_star else 0) := by
      symm
      apply Finset.sum_subset h_sub
      intro x _ hx
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
      simp [hx.1, hx.2]
    rw [h_eq, Finset.sum_pair hq_ne'.symm]
    simp [hq_ne']
    ring

lemma ghz_separating_functional_matrix_make_v_row_star_ne_zero {N : ℕ} (A_r : Fin N → ℂ) (j_star : Fin N) (q : Fin N)
    (hq_nonzero : A_r j_star ≠ 0 → A_r q ≠ 0) :
    ghz_separating_functional_matrix_make_v_row A_r j_star q j_star ≠ 0 := by
  dsimp [ghz_separating_functional_matrix_make_v_row]
  split_ifs with h0
  · simp
  · simp [hq_nonzero h0]

lemma ghz_separating_functional_matrix_make_v_row_eq_zero {N : ℕ} (A_r : Fin N → ℂ) (j_star : Fin N) (q : Fin N)
    (k : Fin N) (hk : k ≠ j_star) (hq : A_r j_star = 0 ∨ q ≠ k) :
    ghz_separating_functional_matrix_make_v_row A_r j_star q k = 0 := by
  dsimp [ghz_separating_functional_matrix_make_v_row]
  split_ifs with h0
  · simp [hk]
  · cases hq with
    | inl h0' => contradiction
    | inr hqk =>
      have : k ≠ q := Ne.symm hqk
      simp [hk, this]

lemma ghz_separating_functional_matrix_sum_prod_ne_zero {M K : Type*} [Fintype M] [Fintype K] [DecidableEq K]
    (j_star : K) (v : M → K → ℂ)
    (h_star : ∀ r : M, v r j_star ≠ 0)
    (h_zero : ∀ k : K, k ≠ j_star → ∃ r : M, v r k = 0) :
    (∑ j : K, ∏ r : M, v r j) ≠ 0 := by
  have h_prod_star : (∏ r : M, v r j_star) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro r _
    exact h_star r
  have h_prod_other : ∀ k : K, k ≠ j_star → (∏ r : M, v r k) = 0 := by
    intro k hk
    obtain ⟨r, hr⟩ := h_zero k hk
    exact Finset.prod_eq_zero (Finset.mem_univ r) hr
  have h_sum : (∑ j : K, ∏ r : M, v r j) = ∏ r : M, v r j_star := by
    rw [Fintype.sum_eq_single j_star]
    intro k hk
    exact h_prod_other k hk
  rw [h_sum]
  exact h_prod_star

lemma ghz_separating_functional_matrix_case_zero_col (N : ℕ) (hN : 4 ≤ N)
    (A : Matrix (Fin (N - 1)) (Fin N) ℂ) (j0 : Fin N)
    (hj0 : ∀ r : Fin (N - 1), A r j0 = 0) :
    ∃ v : Fin (N - 1) → Fin N → ℂ,
      (∀ r : Fin (N - 1), ∑ j : Fin N, A r j * v r j = 0) ∧
      (∑ j : Fin N, ∏ r : Fin (N - 1), v r j) ≠ 0 := by
  classical
  let v : Fin (N - 1) → Fin N → ℂ := fun _ j => if j = j0 then 1 else 0
  refine ⟨v, ?_, ?_⟩
  · intro r
    have : (∑ j : Fin N, A r j * v r j) = A r j0 * v r j0 := by
      rw [Fintype.sum_eq_single j0]
      intro j hj
      simp [v, hj]
    rw [this, hj0 r]
    simp
  · have hprod : ∀ j, (∏ r : Fin (N - 1), v r j) = if j = j0 then 1 else 0 := by
      intro j
      split_ifs with hj
      · simp [v, hj]
      · have : ∃ r : Fin (N - 1), v r j = 0 := by
          have hr0 : 0 < N - 1 := by omega
          refine ⟨⟨0, hr0⟩, ?_⟩
          simp [v, hj]
        obtain ⟨r, hr⟩ := this
        exact Finset.prod_eq_zero (Finset.mem_univ r) hr
    have : (∑ j : Fin N, ∏ r : Fin (N - 1), v r j) = 1 := by
      simp_rw [hprod]
      rw [Fintype.sum_eq_single j0]
      · simp
      · intro j hj
        simp [hj]
    rw [this]
    exact one_ne_zero

lemma ghz_separating_functional_matrix_exists_unblocked (N : ℕ) (hN : 4 ≤ N) (A : Matrix (Fin (N - 1)) (Fin N) ℂ) :
    ∃ j : Fin N, ¬ ∃ r : Fin (N - 1), A r j ≠ 0 ∧ ∀ j', j' ≠ j → A r j' = 0 := by
  classical
  let S : Finset (Fin N) := Finset.univ.filter (fun j => ∃ r : Fin (N - 1), A r j ≠ 0 ∧ ∀ j', j' ≠ j → A r j' = 0)
  have h_inj : ∃ f : {j // j ∈ S} → Fin (N - 1), Function.Injective f := by
    choose r hr using fun (j : {j // j ∈ S}) => (Finset.mem_filter.mp j.2).2
    refine ⟨r, fun j1 j2 heq => Subtype.ext ?_⟩
    have h1 := hr j1
    have h2 := hr j2
    rw [heq] at h1
    by_contra hne
    have := h1.2 j2.1 (Ne.symm hne)
    exact h2.1 this
  rcases h_inj with ⟨f, hf⟩
  have h_card := Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe, Fintype.card_fin] at h_card
  have hN_lt : N - 1 < N := Nat.sub_lt (by omega) (by omega)
  have hS_lt : S.card < Fintype.card (Fin N) := by
    rw [Fintype.card_fin]
    omega
  have h_ss : ∃ j, j ∉ S := by
    by_contra! h_all
    have hS_eq : S = Finset.univ := by
      ext x
      simp [h_all x]
    rw [hS_eq, Finset.card_univ, Fintype.card_fin] at hS_lt
    exact lt_irrefl _ hS_lt
  obtain ⟨j, hj⟩ := h_ss
  refine ⟨j, ?_⟩
  intro h
  apply hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, h⟩

lemma ghz_separating_functional_matrix_exists_third_col (N : ℕ) (hN : 4 ≤ N) (j_star k : Fin N) :
    ∃ j0 : Fin N, j0 ≠ j_star ∧ j0 ≠ k := by
  have h_le : ({j_star, k} : Finset (Fin N)).card ≤ 2 := Finset.card_insert_le j_star {k}
  have h_diff : 0 < (Finset.univ \ ({j_star, k} : Finset (Fin N))).card := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j0, hj0⟩ := Finset.card_pos.mp h_diff
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hj0
  exact ⟨j0, hj0.1, hj0.2⟩

lemma ghz_separating_functional_matrix_exists_other_row (N : ℕ) (hN : 4 ≤ N) (r_star : Fin (N - 1)) :
    ∃ r' : Fin (N - 1), r' ≠ r_star := by
  have : 1 < Fintype.card (Fin (N - 1)) := by
    rw [Fintype.card_fin]
    omega
  have : Nontrivial (Fin (N - 1)) := Fintype.one_lt_card_iff_nontrivial.mp this
  exact exists_ne r_star

lemma ghz_separating_functional_matrix_exists_choice_p (N : ℕ) (hN : 4 ≤ N) (A : Matrix (Fin (N - 1)) (Fin N) ℂ)
    (j_star : Fin N)
    (hunb : ¬ ∃ r : Fin (N - 1), A r j_star ≠ 0 ∧ ∀ j', j' ≠ j_star → A r j' = 0) :
    ∃ p : Fin (N - 1) → Fin N,
      (∀ r, p r ≠ j_star) ∧
      (∀ r, A r j_star ≠ 0 → A r (p r) ≠ 0) := by
  have h_ex : ∀ r : Fin (N - 1), ∃ q : Fin N, q ≠ j_star ∧ (A r j_star ≠ 0 → A r q ≠ 0) := by
    intro r
    by_cases hr : A r j_star = 0
    · have : 1 < Fintype.card (Fin N) := by rw [Fintype.card_fin]; omega
      have : Nontrivial (Fin N) := Fintype.one_lt_card_iff_nontrivial.mp this
      obtain ⟨q, hq⟩ := exists_ne j_star
      exact ⟨q, hq, fun h => (h hr).elim⟩
    · by_contra! h
      apply hunb
      refine ⟨r, hr, fun j' hj' => (h j' hj').2⟩
  choose p hp using h_ex
  exact ⟨p, fun r => (hp r).1, fun r => (hp r).2⟩

lemma ghz_separating_functional_matrix_finish (N : ℕ) (A : Matrix (Fin (N - 1)) (Fin N) ℂ)
    (j_star : Fin N) (q : Fin (N - 1) → Fin N)
    (hq_ne : ∀ r, A r j_star ≠ 0 → q r ≠ j_star)
    (hq_nonzero : ∀ r, A r j_star ≠ 0 → A r (q r) ≠ 0)
    (h_zero : ∀ k : Fin N, k ≠ j_star → ∃ r : Fin (N - 1), A r j_star = 0 ∨ q r ≠ k) :
    ∃ v : Fin (N - 1) → Fin N → ℂ,
      (∀ r : Fin (N - 1), ∑ j : Fin N, A r j * v r j = 0) ∧
      (∑ j : Fin N, ∏ r : Fin (N - 1), v r j) ≠ 0 := by
  let v : Fin (N - 1) → Fin N → ℂ := fun r => ghz_separating_functional_matrix_make_v_row (A r) j_star (q r)
  refine ⟨v, ?_, ?_⟩
  · intro r
    exact ghz_separating_functional_matrix_make_v_row_dot_zero (A r) j_star (q r) (hq_ne r)
  · apply ghz_separating_functional_matrix_sum_prod_ne_zero j_star v
    · intro r
      exact ghz_separating_functional_matrix_make_v_row_star_ne_zero (A r) j_star (q r) (hq_nonzero r)
    · intro k hk
      obtain ⟨r, hr⟩ := h_zero k hk
      refine ⟨r, ghz_separating_functional_matrix_make_v_row_eq_zero (A r) j_star (q r) k hk hr⟩

/-- Separating functional lemma: for every (N - 1) x N complex matrix with N ≥ 4, there exist row vectors satisfying the row vanishing equations whose diagonal product sum is nonzero. -/
theorem ghz_separating_functional_matrix (N : ℕ) (hN : 4 ≤ N)
    (A : Matrix (Fin (N - 1)) (Fin N) ℂ) :
    ∃ v : Fin (N - 1) → Fin N → ℂ,
      (∀ r : Fin (N - 1), ∑ j : Fin N, A r j * v r j = 0) ∧
      (∑ j : Fin N, ∏ r : Fin (N - 1), v r j) ≠ 0 := by
  classical
  by_cases h_zero_col : ∃ j0 : Fin N, ∀ r : Fin (N - 1), A r j0 = 0
  · obtain ⟨j0, hj0⟩ := h_zero_col
    exact ghz_separating_functional_matrix_case_zero_col N hN A j0 hj0
  have h_no_zero : ∀ j : Fin N, ∃ r : Fin (N - 1), A r j ≠ 0 := by
    intro j
    by_contra! hj
    exact h_zero_col ⟨j, hj⟩
  obtain ⟨j_star, hj_star⟩ := ghz_separating_functional_matrix_exists_unblocked N hN A
  obtain ⟨p, hp_ne, hp_nonzero⟩ := ghz_separating_functional_matrix_exists_choice_p N hN A j_star hj_star
  by_cases h_has_zero : ∃ r0 : Fin (N - 1), A r0 j_star = 0
  · obtain ⟨r0, hr0⟩ := h_has_zero
    apply ghz_separating_functional_matrix_finish N A j_star p (fun r _ => hp_ne r) hp_nonzero
    intro k _
    exact ⟨r0, Or.inl hr0⟩
  have h_all_nonzero : ∀ r : Fin (N - 1), A r j_star ≠ 0 := by
    intro r
    by_contra hr
    exact h_has_zero ⟨r, hr⟩
  by_cases h_all_eq : ∀ r1 r2 : Fin (N - 1), p r1 = p r2
  · have hr0 : 0 < N - 1 := by omega
    let r_init : Fin (N - 1) := ⟨0, hr0⟩
    let k := p r_init
    have hk_ne : k ≠ j_star := hp_ne r_init
    have hp_k : ∀ r, p r = k := fun r => h_all_eq r r_init
    obtain ⟨j0, hj0_star, hj0_k⟩ := ghz_separating_functional_matrix_exists_third_col N hN j_star k
    obtain ⟨r_star, hr_star⟩ := h_no_zero j0
    obtain ⟨r_other, hr_other⟩ := ghz_separating_functional_matrix_exists_other_row N hN r_star
    let q : Fin (N - 1) → Fin N := fun r => if r = r_star then j0 else k
    apply ghz_separating_functional_matrix_finish N A j_star q
    · intro r _
      dsimp [q]
      split_ifs with hr
      · exact hj0_star
      · exact hk_ne
    · intro r _
      dsimp [q]
      split_ifs with hr
      · subst hr
        exact hr_star
      · rw [← hp_k r]
        exact hp_nonzero r (h_all_nonzero r)
    · intro k' hk'
      by_cases hk'_eq : k' = j0
      · refine ⟨r_other, Or.inr ?_⟩
        dsimp [q]
        rw [if_neg hr_other]
        rw [hk'_eq]
        exact hj0_k.symm
      · refine ⟨r_star, Or.inr ?_⟩
        dsimp [q]
        rw [if_pos rfl]
        exact Ne.symm hk'_eq
  · have h_ex_ne : ∃ r1 r2 : Fin (N - 1), p r1 ≠ p r2 := by
      by_contra! h
      exact h_all_eq h
    obtain ⟨r1, r2, hr12⟩ := h_ex_ne
    apply ghz_separating_functional_matrix_finish N A j_star p (fun r _ => hp_ne r) hp_nonzero
    intro k' _
    by_cases hk'_r1 : p r1 = k'
    · refine ⟨r2, Or.inr ?_⟩
      rw [← hk'_r1]
      exact hr12.symm
    · exact ⟨r1, Or.inr hk'_r1⟩
