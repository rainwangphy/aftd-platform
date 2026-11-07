import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialLogConcave
import AFTD.Kb.Tcs.PetrialCoeff
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# op_1239_at_most_two_nonzero_coeffs_log_concave

Topic: combinatorics   Node: 2af54d669776

Provenance: formalization of a published result. Source: arXiv:2611.07503, Section 2

Every simple graph G on a finite type V with decidable equality and decidable adjacency for which the number of k in the range from 0 to Fintype.card V + 1 with petrial_coeff G k ≠ 0 is at most 2 satisfies petrial_log_concave G.
-/

lemma op_1239_at_most_two_nonzero_coeffs_log_concave_matrix_rank_add_le
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {K : Type*} [Field K] (A B : Matrix m n K) :
    (A + B).rank ≤ A.rank + B.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  have hle : LinearMap.range (A.mulVecLin + B.mulVecLin) ≤ LinearMap.range A.mulVecLin ⊔ LinearMap.range B.mulVecLin :=
    LinearMap.range_add_le _ _
  have h1 := Submodule.finrank_mono hle
  have h2 := Submodule.finrank_add_le_finrank_add_finrank (LinearMap.range A.mulVecLin) (LinearMap.range B.mulVecLin)
  omega

lemma op_1239_at_most_two_nonzero_coeffs_log_concave_rank_single_diag_le
    {V : Type*} [Fintype V] [DecidableEq V] (v : V) :
    (Matrix.diagonal (fun w => if w = v then (1 : ZMod 2) else 0)).rank ≤ 1 := by
  rw [Matrix.rank_diagonal]
  rw [Fintype.card_subtype]
  have : (Finset.univ.filter (fun w => (if w = v then (1 : ZMod 2) else 0) ≠ 0)) ⊆ {v} := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
    split_ifs at hw with h
    · exact Finset.mem_singleton.mpr h
    · contradiction
  have hsub := Finset.card_le_card this
  simp only [Finset.card_singleton] at hsub
  exact hsub

lemma op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_insert
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset V) (v : V) (hv : v ∉ F) :
    petrial_matrix G (insert v F) =
      petrial_matrix G F + Matrix.diagonal (fun w => if w = v then (1 : ZMod 2) else 0) := by
  unfold petrial_matrix
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_apply, Finset.mem_insert]
  by_cases hij : i = j
  · subst hij
    by_cases hiv : i = v
    · subst hiv
      simp [hv]
    · simp [hiv]
  · simp [hij]

lemma op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_remove
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset V) (v : V) (hv : v ∉ F) :
    petrial_matrix G F =
      petrial_matrix G (insert v F) + Matrix.diagonal (fun w => if w = v then (1 : ZMod 2) else 0) := by
  unfold petrial_matrix
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_apply, Finset.mem_insert]
  by_cases hij : i = j
  · subst hij
    by_cases hiv : i = v
    · subst hiv
      have : (1 : ZMod 2) + 1 = 0 := rfl
      simp [hv, this]
    · simp [hiv]
  · simp [hij]

lemma op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_rank_insert_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset V) (v : V) (hv : v ∉ F) :
    (petrial_matrix G (insert v F)).rank ≤ (petrial_matrix G F).rank + 1 := by
  rw [op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_insert G F v hv]
  have := op_1239_at_most_two_nonzero_coeffs_log_concave_matrix_rank_add_le (petrial_matrix G F)
    (Matrix.diagonal (fun w => if w = v then (1 : ZMod 2) else 0))
  have h1 := op_1239_at_most_two_nonzero_coeffs_log_concave_rank_single_diag_le v
  omega

lemma op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_rank_erase_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (F : Finset V) (v : V) (hv : v ∉ F) :
    (petrial_matrix G F).rank ≤ (petrial_matrix G (insert v F)).rank + 1 := by
  rw [op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_remove G F v hv]
  have := op_1239_at_most_two_nonzero_coeffs_log_concave_matrix_rank_add_le (petrial_matrix G (insert v F))
    (Matrix.diagonal (fun w => if w = v then (1 : ZMod 2) else 0))
  have h1 := op_1239_at_most_two_nonzero_coeffs_log_concave_rank_single_diag_le v
  omega

lemma op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_rank_erase_le'
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (v : V) (hv : v ∈ A) :
    (petrial_matrix G (A.erase v)).rank ≤ (petrial_matrix G A).rank + 1 := by
  have hnot : v ∉ A.erase v := by simp
  have hins : insert v (A.erase v) = A := Finset.insert_erase hv
  have := op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_rank_erase_le G (A.erase v) v hnot
  rwa [hins] at this

lemma op_1239_at_most_two_nonzero_coeffs_log_concave_exists_intermediate_rank
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    ∀ (n : ℕ) (A B : Finset V), (A \ B).card + (B \ A).card = n →
      ∀ k : ℕ, (petrial_matrix G A).rank ≤ k → k ≤ (petrial_matrix G B).rank →
      ∃ C : Finset V, (petrial_matrix G C).rank = k := by
  intro n
  induction' n using Nat.strong_induction_on with n ih
  intro A B hn k hA hB
  by_cases hAB_sdiff : (A \ B).card = 0
  · by_cases hBA_sdiff : (B \ A).card = 0
    · have h_eq : A = B := by
        rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at hAB_sdiff hBA_sdiff
        exact Finset.Subset.antisymm hAB_sdiff hBA_sdiff
      subst h_eq
      exact ⟨A, by omega⟩
    · obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hBA_sdiff)
      have hvB : v ∈ B := (Finset.mem_sdiff.mp hv).1
      have hvA : v ∉ A := (Finset.mem_sdiff.mp hv).2
      have hstep : ((insert v A) \ B).card + (B \ (insert v A)).card + 1 = (A \ B).card + (B \ A).card := by
        have h1 : (insert v A) \ B = A \ B := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert]
          constructor
          · rintro ⟨h1 | h1, h2⟩
            · subst h1; contradiction
            · exact ⟨h1, h2⟩
          · rintro ⟨h1, h2⟩
            exact ⟨Or.inr h1, h2⟩
        have h2 : B \ (insert v A) = (B \ A).erase v := by
          ext x
          simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
          tauto
        rw [h1, h2]
        have hcard := Finset.card_erase_of_mem hv
        have hpos : 1 ≤ (B \ A).card := Finset.card_pos.mpr ⟨v, hv⟩
        omega
      have hlt : ((insert v A) \ B).card + (B \ (insert v A)).card < n := by omega
      have hle_ins := op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_rank_insert_le G A v hvA
      by_cases hk_ins : (petrial_matrix G (insert v A)).rank ≤ k
      · exact ih _ hlt (insert v A) B rfl k hk_ins hB
      · have : (petrial_matrix G A).rank = k := by omega
        exact ⟨A, this⟩
  · obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hAB_sdiff)
    have hvA : v ∈ A := (Finset.mem_sdiff.mp hv).1
    have hvB : v ∉ B := (Finset.mem_sdiff.mp hv).2
    have hstep : ((A.erase v) \ B).card + (B \ (A.erase v)).card + 1 = (A \ B).card + (B \ A).card := by
      have h1 : (A.erase v) \ B = (A \ B).erase v := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        tauto
      have h2 : B \ (A.erase v) = B \ A := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_erase]
        constructor
        · rintro ⟨hxB, hx⟩
          refine ⟨hxB, ?_⟩
          rintro hxA
          exact hx ⟨fun hxv => hvB (hxv ▸ hxB), hxA⟩
        · rintro ⟨hxB, hxA⟩
          exact ⟨hxB, fun ⟨_, h⟩ => hxA h⟩
      rw [h1, h2]
      have hcard := Finset.card_erase_of_mem hv
      have hpos : 1 ≤ (A \ B).card := Finset.card_pos.mpr ⟨v, hv⟩
      omega
    have hlt : ((A.erase v) \ B).card + (B \ (A.erase v)).card < n := by omega
    have hle_erase := op_1239_at_most_two_nonzero_coeffs_log_concave_petrial_matrix_rank_erase_le' G A v hvA
    by_cases hk_erase : (petrial_matrix G (A.erase v)).rank ≤ k
    · exact ih _ hlt (A.erase v) B rfl k hk_erase hB
    · have : (petrial_matrix G A).rank = k := by omega
      exact ⟨A, this⟩

/-- Graphs with at most two nonzero Petrial coefficients have log-concave partial Petrial polynomials. -/
theorem op_1239_at_most_two_nonzero_coeffs_log_concave
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ((Finset.range (Fintype.card V + 1)).filter (fun k => petrial_coeff G k ≠ 0)).card ≤ 2) :
    petrial_log_concave G := by
  intro k hi hj
  obtain ⟨i, hik, hic⟩ := hi
  obtain ⟨j, hkj, hjc⟩ := hj
  obtain ⟨Fi, hFi⟩ := Finset.card_ne_zero.mp hic
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hFi
  obtain ⟨Fj, hFj⟩ := Finset.card_ne_zero.mp hjc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hFj
  have hFi_rank : (petrial_matrix G Fi).rank ≤ k := by rw [hFi]; omega
  have hFj_rank : k ≤ (petrial_matrix G Fj).rank := by rw [hFj]; omega
  obtain ⟨Fk, hFk⟩ := op_1239_at_most_two_nonzero_coeffs_log_concave_exists_intermediate_rank
    G ((Fi \ Fj).card + (Fj \ Fi).card) Fi Fj rfl k hFi_rank hFj_rank
  have hkc : petrial_coeff G k ≠ 0 := by
    unfold petrial_coeff
    intro h0
    have hmem : Fk ∈ (Finset.univ : Finset (Finset V)).filter (fun F' => (petrial_matrix G F').rank = k) := by
      simp [hFk]
    have : (Finset.univ.filter (fun F' => (petrial_matrix G F').rank = k)).card ≠ 0 :=
      Finset.card_ne_zero.mpr ⟨Fk, hmem⟩
    exact this h0
  have hi_le : i ≤ Fintype.card V := by
    have := Matrix.rank_le_card_width (petrial_matrix G Fi)
    omega
  have hj_le : j ≤ Fintype.card V := by
    have := Matrix.rank_le_card_width (petrial_matrix G Fj)
    omega
  let S := (Finset.range (Fintype.card V + 1)).filter (fun m => petrial_coeff G m ≠ 0)
  have hi_in : i ∈ S := by
    simp only [Finset.mem_filter, Finset.mem_range, S]
    exact ⟨by omega, hic⟩
  have hj_in : j ∈ S := by
    simp only [Finset.mem_filter, Finset.mem_range, S]
    exact ⟨by omega, hjc⟩
  have hk_in : k ∈ S := by
    simp only [Finset.mem_filter, Finset.mem_range, S]
    exact ⟨by omega, hkc⟩
  have h_sub : {i, k, j} ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact hi_in
    · exact hk_in
    · exact hj_in
  have h_card_three : ({i, k, j} : Finset ℕ).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton]
      omega
    · simp only [Finset.mem_insert, Finset.mem_singleton]
      rintro (rfl | rfl) <;> omega
  have h_le := Finset.card_le_card h_sub
  rw [h_card_three] at h_le
  change S.card ≤ 2 at h
  exfalso
  omega
