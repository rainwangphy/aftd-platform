import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinTableaux
import AFTD.Kb.Tcs.LatinTableauxCount
import AFTD.Kb.Tcs.LatinTopRowAvailability
import AFTD.Kb.Tcs.LatinDoubleThreeTailShapeRowLenSucc
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfileSucc
import AFTD.Kb.Tcs.LatinDoubleThreeTailShapeRowLen
import AFTD.Kb.Tcs.MemLatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfile

/-!
# latin_double_three_tail_count_step

Topic: combinatorics   Node: 294941133e7f

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

The number of tableaux of the next shape is the sum of availability permanents over all tableaux of the previous shape.
-/

theorem latin_double_three_tail_count_step_top_lt (k : ℕ) (hk : 2 ≤ k) (c : (latin_double_three_tail_shape (k + 1)).cells)
    (h0 : c.1.1 = 0) : c.1.2 < k + 1 := by
  have h := (mem_latin_double_three_tail_shape (k + 1) c.1.1 c.1.2).mp c.2
  rw [h0, Nat.sub_zero, max_eq_right (by omega)] at h
  exact h.2

theorem latin_double_three_tail_count_step_low_mem (k : ℕ) (c : (latin_double_three_tail_shape (k + 1)).cells)
    (h0 : c.1.1 ≠ 0) : (c.1.1 - 1, c.1.2) ∈ (latin_double_three_tail_shape k).cells := by
  have h := (mem_latin_double_three_tail_shape (k + 1) c.1.1 c.1.2).mp c.2
  apply (mem_latin_double_three_tail_shape k (c.1.1 - 1) c.1.2).mpr
  have : k - (c.1.1 - 1) = k + 1 - c.1.1 := by omega
  rw [this]
  exact ⟨by omega, h.2⟩

def latin_double_three_tail_count_step_ext (k : ℕ) (hk : 2 ≤ k) (T : (latin_double_three_tail_shape k).cells → ℕ)
    (σ : Equiv.Perm (Fin (k + 1))) : (latin_double_three_tail_shape (k + 1)).cells → ℕ :=
  fun c => if h : c.1.1 = 0 then (σ ⟨c.1.2, latin_double_three_tail_count_step_top_lt k hk c h⟩).val + 1
    else T ⟨(c.1.1 - 1, c.1.2), latin_double_three_tail_count_step_low_mem k c h⟩

theorem latin_double_three_tail_count_step_row0 (k : ℕ) (hk : 2 ≤ k) :
    (latin_double_three_tail_shape (k + 1)).rowLen 0 = k + 1 := by
  rw [latin_double_three_tail_shape_rowLen, if_pos (by omega)]
  exact max_eq_right (by omega)

theorem latin_double_three_tail_count_step_top_bound (k : ℕ) (hk : 2 ≤ k) (T' : (latin_double_three_tail_shape (k + 1)).cells → ℕ)
    (hT : T' ∈ latin_tableaux (latin_double_three_tail_shape (k + 1))) (j : ℕ) (hj : j < k + 1) :
    1 ≤ T' ⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j (by omega) hj⟩ ∧
      T' ⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j (by omega) hj⟩ ≤ k + 1 := by
  simp only [latin_tableaux, Finset.mem_filter, Fintype.mem_piFinset] at hT
  have h := hT.1 ⟨(0, j), latin_double_three_tail_profile_succ_top_mem k j (by omega) hj⟩
  simp only [latin_double_three_tail_count_step_row0 k hk, Finset.mem_Icc] at h
  exact h

noncomputable def latin_double_three_tail_count_step_perm (k : ℕ) (hk : 2 ≤ k) (T' : (latin_double_three_tail_shape (k + 1)).cells → ℕ)
    (hT : T' ∈ latin_tableaux (latin_double_three_tail_shape (k + 1))) : Equiv.Perm (Fin (k + 1)) :=
  Equiv.ofBijective (fun j => ⟨T' ⟨(0, j.val), latin_double_three_tail_profile_succ_top_mem k j.val (by omega) j.isLt⟩ - 1,
    by have := latin_double_three_tail_count_step_top_bound k hk T' hT j.val j.isLt; omega⟩)
    (Finite.injective_iff_bijective.mp (by
      intro a b hab
      simp only [Fin.mk.injEq] at hab
      have ha := latin_double_three_tail_count_step_top_bound k hk T' hT a.val a.isLt
      have hb := latin_double_three_tail_count_step_top_bound k hk T' hT b.val b.isLt
      have heq : T' ⟨(0, a.val), latin_double_three_tail_profile_succ_top_mem k a.val (by omega) a.isLt⟩ =
          T' ⟨(0, b.val), latin_double_three_tail_profile_succ_top_mem k b.val (by omega) b.isLt⟩ := by omega
      simp only [latin_tableaux, Finset.mem_filter] at hT
      exact Fin.ext (hT.2.1 ⟨(0, a.val), latin_double_three_tail_profile_succ_top_mem k a.val (by omega) a.isLt⟩
        ⟨(0, b.val), latin_double_three_tail_profile_succ_top_mem k b.val (by omega) b.isLt⟩ rfl heq)))

theorem latin_double_three_tail_count_step_perm_apply (k : ℕ) (hk : 2 ≤ k) (T' : (latin_double_three_tail_shape (k + 1)).cells → ℕ)
    (hT : T' ∈ latin_tableaux (latin_double_three_tail_shape (k + 1))) (j : Fin (k + 1)) :
    ((latin_double_three_tail_count_step_perm k hk T' hT j).val : ℕ) + 1 =
      T' ⟨(0, j.val), latin_double_three_tail_profile_succ_top_mem k j.val (by omega) j.isLt⟩ := by
  have := latin_double_three_tail_count_step_top_bound k hk T' hT j.val j.isLt
  simp only [latin_double_three_tail_count_step_perm, Equiv.ofBijective_apply]
  omega

theorem latin_double_three_tail_count_step_fiber (k : ℕ) (hk : 2 ≤ k) (T : (latin_double_three_tail_shape k).cells → ℕ)
    (hT : T ∈ latin_tableaux (latin_double_three_tail_shape k)) :
    ((latin_tableaux (latin_double_three_tail_shape (k + 1))).filter
      (fun T' => latin_double_three_tail_profile_succ_restrict k T' = T)).card =
    (Finset.univ.filter (fun σ : Equiv.Perm (Fin (k + 1)) => ∀ j : Fin (k + 1),
      ∀ c : (latin_double_three_tail_shape k).cells, c.val.2 = j.val → T c ≠ (σ j).val + 1)).card := by
  have hT' := hT
  simp only [latin_tableaux, Finset.mem_filter, Fintype.mem_piFinset] at hT'
  obtain ⟨hb, hr, hcl⟩ := hT'
  refine Finset.card_bij' (fun T' h => latin_double_three_tail_count_step_perm k hk T' (Finset.mem_filter.mp h).1)
    (fun σ _ => latin_double_three_tail_count_step_ext k hk T σ) (hi := ?_) (hj := ?_) (left_inv := ?_) (right_inv := ?_)
  · intro T' h
    obtain ⟨hT1, hres⟩ := Finset.mem_filter.mp h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    intro j c hcj heq
    rw [latin_double_three_tail_count_step_perm_apply] at heq
    rw [← hres] at heq
    have hT1' := hT1
    simp only [latin_tableaux, Finset.mem_filter] at hT1'
    have := hT1'.2.2 _ _ hcj heq
    simp at this
  · intro σ hσ
    have hσ := (Finset.mem_filter.mp hσ).2
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · simp only [latin_tableaux, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun c => ?_, fun c1 c2 h1 h2 => ?_, fun c1 c2 h1 h2 => ?_⟩
      · simp only [latin_double_three_tail_count_step_ext]
        split_ifs with h0
        · rw [Finset.mem_Icc, h0, latin_double_three_tail_count_step_row0 k hk]
          exact ⟨by omega, by have := (σ ⟨c.1.2, latin_double_three_tail_count_step_top_lt k hk c h0⟩).isLt; omega⟩
        · have := hb ⟨(c.1.1 - 1, c.1.2), latin_double_three_tail_count_step_low_mem k c h0⟩
          have e2 : (latin_double_three_tail_shape (k + 1)).rowLen c.1.1 =
              (latin_double_three_tail_shape k).rowLen (c.1.1 - 1) := by
            have := latin_double_three_tail_shape_rowLen_succ k (c.1.1 - 1)
            rwa [Nat.sub_add_cancel (by omega)] at this
          rw [e2]
          exact this
      · simp only [latin_double_three_tail_count_step_ext] at h2
        by_cases h0 : c1.1.1 = 0
        · have h0' : c2.1.1 = 0 := by omega
          rw [dif_pos h0, dif_pos h0'] at h2
          have := σ.injective (Fin.ext (by simpa using h2))
          simpa using this
        · have h0' : c2.1.1 ≠ 0 := by omega
          rw [dif_neg h0, dif_neg h0'] at h2
          exact hr _ _ (by simp [h1]) h2
      · simp only [latin_double_three_tail_count_step_ext] at h2
        by_cases h0 : c1.1.1 = 0 <;> by_cases h0' : c2.1.1 = 0
        · omega
        · rw [dif_pos h0, dif_neg h0'] at h2
          exact absurd h2.symm (hσ ⟨c1.1.2, latin_double_three_tail_count_step_top_lt k hk c1 h0⟩ _ (by simp [h1]))
        · rw [dif_neg h0, dif_pos h0'] at h2
          exact absurd h2 (hσ ⟨c2.1.2, latin_double_three_tail_count_step_top_lt k hk c2 h0'⟩ _ (by simp [h1]))
        · rw [dif_neg h0, dif_neg h0'] at h2
          have := hcl _ _ (by simp [h1]) h2
          simp at this
          omega
    · funext c
      simp only [latin_double_three_tail_profile_succ_restrict, latin_double_three_tail_count_step_ext]
      rw [dif_neg (by simp)]
      congr 1
  · intro T' h
    obtain ⟨hT1, hres⟩ := Finset.mem_filter.mp h
    funext c
    simp only [latin_double_three_tail_count_step_ext]
    split_ifs with h0
    · rw [latin_double_three_tail_count_step_perm_apply]
      congr 1
      exact Subtype.ext (Prod.ext h0.symm rfl)
    · rw [← hres]
      simp only [latin_double_three_tail_profile_succ_restrict]
      congr 1
      exact Subtype.ext (Prod.ext (by simp; omega) rfl)
  · intro σ hσ
    ext j
    simp [latin_double_three_tail_count_step_perm, latin_double_three_tail_count_step_ext]

theorem latin_double_three_tail_count_step (k : ℕ) (hk : 5 ≤ k) : latin_tableaux_count (latin_double_three_tail_shape (k+1)) = ∑ T ∈ latin_tableaux (latin_double_three_tail_shape k), Matrix.permanent (latin_top_row_availability (latin_double_three_tail_shape k) T (k+1)) := by
  have _hsucc := @latin_double_three_tail_profile_succ
  unfold latin_tableaux_count
  rw [Finset.card_eq_sum_card_fiberwise (f := latin_double_three_tail_profile_succ_restrict k)
    (t := latin_tableaux (latin_double_three_tail_shape k))
    (fun T' hT' => latin_double_three_tail_profile_succ_restrict_mem k T' hT')]
  refine Finset.sum_congr rfl fun T hT => ?_
  rw [latin_double_three_tail_count_step_fiber k (by omega) T hT, Finset.card_filter]
  unfold Matrix.permanent latin_top_row_availability
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.prod_boole]
  simp only [Finset.mem_univ, true_imp_iff]
