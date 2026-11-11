import AFTD.Prelude
import AFTD.Kb.NumberTheory.PlrsSeq
import AFTD.Kb.NumberTheory.IsCompleteSequence

/-!
# leading_unit_monotonicity_length_two

Topic: elementary_number_theory   Node: 7790f59a1d79

Provenance: helper lemma. arXiv:2611.10200, Section 1

For any natural number N with 1 ≤ N, if is_complete_sequence (plrs_seq [1, N]) holds, then is_complete_sequence (plrs_seq [1, 1, N]) holds.
-/

private lemma leading_unit_monotonicity_length_two_val1 (N : ℕ) :
    plrs_seq [1, N] 1 = 1 := plrs_seq.eq_2 _

private lemma leading_unit_monotonicity_length_two_val2 (N : ℕ) :
    plrs_seq [1, N] 2 = 2 := by
  rw [plrs_seq.eq_3]
  norm_num
  rw [leading_unit_monotonicity_length_two_val1]
  norm_num

private lemma leading_unit_monotonicity_length_two_rec1 (N n : ℕ) (hn : 1 ≤ n) :
    plrs_seq [1, N] (n + 2) = plrs_seq [1, N] (n + 1) + (N : ℤ) * plrs_seq [1, N] n := by
  rw [plrs_seq.eq_3]
  have hlen : ¬ (n + 2 ≤ [1,N].length) := by simp; omega
  rw [if_neg hlen]
  rw [show [1,N].length = 2 from rfl, show 2 = 1 + 1 from rfl,
      Finset.sum_range_succ, Finset.sum_range_one]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.cast_one]
  have e1 : n + 1 - 0 = n + 1 := by omega
  have e2 : n + 1 - 1 = n := by omega
  rw [e1, e2]
  ring

private lemma leading_unit_monotonicity_length_two_nonneg1 (N : ℕ) :
    ∀ n, 0 ≤ plrs_seq [1, N] n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [plrs_seq.eq_1]
    | 1 => rw [leading_unit_monotonicity_length_two_val1]; norm_num
    | 2 => rw [leading_unit_monotonicity_length_two_val2]; norm_num
    | k + 3 =>
      rw [show k + 3 = (k + 1) + 2 from rfl,
        leading_unit_monotonicity_length_two_rec1 N (k+1) (by omega)]
      have h1 := ih (k+2) (by omega)
      have h2 := ih (k+1) (by omega)
      have hN : (0:ℤ) ≤ (N:ℤ) := by positivity
      nlinarith [mul_nonneg hN h2]

private lemma leading_unit_monotonicity_length_two_big1 (N : ℕ) (hN : 3 ≤ N) :
    ∀ i, 3 ≤ i → 5 ≤ plrs_seq [1, N] i := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, hi with
    | 3, _ =>
      rw [show (3:ℕ) = 1 + 2 from rfl,
        leading_unit_monotonicity_length_two_rec1 N 1 (by omega)]
      rw [leading_unit_monotonicity_length_two_val1, leading_unit_monotonicity_length_two_val2]
      have : (3:ℤ) ≤ (N:ℤ) := by exact_mod_cast hN
      nlinarith
    | (k + 4), _ =>
      rw [show k + 4 = (k + 2) + 2 from rfl,
        leading_unit_monotonicity_length_two_rec1 N (k+2) (by omega)]
      have hprev := ih (k+3) (by omega) (by omega)
      have hnn := leading_unit_monotonicity_length_two_nonneg1 N (k+2)
      have hN0 : (0:ℤ) ≤ (N:ℤ) := by positivity
      nlinarith [mul_nonneg hN0 hnn]

private lemma leading_unit_monotonicity_length_two_le_two_of_complete (N : ℕ)
    (hcomp : is_complete_sequence (plrs_seq [1, N])) : N ≤ 2 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨S, hS1, hsum⟩ := hcomp 4 (by norm_num)
  have h4 : ∀ i ∈ S, plrs_seq [1, N] i ≤ 4 := by
    intro i hi
    have := Finset.single_le_sum (f := fun i => plrs_seq [1, N] i) (s := S)
      (fun j hj => leading_unit_monotonicity_length_two_nonneg1 N j) hi
    omega
  have hSsub : S ⊆ ({1, 2} : Finset ℕ) := by
    intro i hi
    have hi1 := hS1 i hi
    have hi4 := h4 i hi
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_contra hmem
    push Not at hmem
    have h3 : 3 ≤ i := by omega
    have := leading_unit_monotonicity_length_two_big1 N hcon i h3
    omega
  have hle : ∑ i ∈ S, plrs_seq [1, N] i
      ≤ ∑ i ∈ ({1, 2} : Finset ℕ), plrs_seq [1, N] i :=
    Finset.sum_le_sum_of_subset_of_nonneg hSsub (fun i _ _ => leading_unit_monotonicity_length_two_nonneg1 N i)
  have hsum2 : ∑ i ∈ ({1, 2} : Finset ℕ), plrs_seq [1, N] i = 3 := by
    rw [Finset.sum_insert (by norm_num : (1:ℕ) ∉ ({2} : Finset ℕ))]
    rw [Finset.sum_singleton, leading_unit_monotonicity_length_two_val1,
      leading_unit_monotonicity_length_two_val2]
    norm_num
  omega

private lemma leading_unit_monotonicity_length_two_val11_1 (N : ℕ) :
    plrs_seq [1,1,N] 1 = 1 := plrs_seq.eq_2 _

private lemma leading_unit_monotonicity_length_two_val11_2 (N : ℕ) :
    plrs_seq [1,1,N] 2 = 2 := by
  rw [plrs_seq.eq_3]
  norm_num
  rw [leading_unit_monotonicity_length_two_val11_1]
  norm_num

private lemma leading_unit_monotonicity_length_two_val11_3 (N : ℕ) :
    plrs_seq [1,1,N] 3 = 4 := by
  rw [show (3:ℕ) = 1 + 2 from rfl, plrs_seq.eq_3]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.cast_one]
  have e0 : 1 + 1 - 0 = 2 := by omega
  have e1 : 1 + 1 - 1 = 1 := by omega
  rw [e0, e1, leading_unit_monotonicity_length_two_val11_2,
    leading_unit_monotonicity_length_two_val11_1]
  norm_num

private lemma leading_unit_monotonicity_length_two_rec11 (N n : ℕ) (hn : 2 ≤ n) :
    plrs_seq [1,1,N] (n + 2) =
      plrs_seq [1,1,N] (n+1) + plrs_seq [1,1,N] n + (N:ℤ) * plrs_seq [1,1,N] (n-1) := by
  rw [plrs_seq.eq_3]
  have hlen : ¬ (n + 2 ≤ [1,1,N].length) := by simp; omega
  rw [if_neg hlen]
  rw [show [1,1,N].length = 3 from rfl, show 3 = 2+1 from rfl, Finset.sum_range_succ,
      show 2 = 1+1 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [List.getD_cons_zero, List.getD_cons_succ, Nat.cast_one]
  have e1 : n + 1 - 0 = n + 1 := by omega
  have e2 : n + 1 - 1 = n := by omega
  have e3 : n + 1 - 2 = n - 1 := by omega
  rw [e1, e2, e3]
  ring

private lemma leading_unit_monotonicity_length_two_nonneg11 (N : ℕ) :
    ∀ n, 0 ≤ plrs_seq [1,1,N] n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rw [plrs_seq.eq_1]
    | 1 => norm_num [leading_unit_monotonicity_length_two_val11_1]
    | 2 => norm_num [leading_unit_monotonicity_length_two_val11_2]
    | 3 => norm_num [leading_unit_monotonicity_length_two_val11_3]
    | k + 4 =>
      rw [show k + 4 = (k + 2) + 2 from rfl,
        leading_unit_monotonicity_length_two_rec11 N (k+2) (by omega)]
      have e1 : k + 2 + 1 = k + 3 := by ring
      have e2 : k + 2 - 1 = k + 1 := by omega
      rw [e1, e2]
      have h1 := ih (k+3) (by omega)
      have h2 := ih (k+2) (by omega)
      have h3 := ih (k+1) (by omega)
      have hN : (0:ℤ) ≤ (N:ℤ) := by positivity
      nlinarith [mul_nonneg hN h3]

private lemma leading_unit_monotonicity_length_two_pos11 (N : ℕ) :
    ∀ i, 1 ≤ i → 1 ≤ plrs_seq [1,1,N] i := by
  intro i hi
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    match i, hi with
    | 1, _ => norm_num [leading_unit_monotonicity_length_two_val11_1]
    | 2, _ => norm_num [leading_unit_monotonicity_length_two_val11_2]
    | 3, _ => norm_num [leading_unit_monotonicity_length_two_val11_3]
    | (k + 4), _ =>
      rw [show k + 4 = (k + 2) + 2 from rfl,
        leading_unit_monotonicity_length_two_rec11 N (k+2) (by omega)]
      have e1 : k + 2 + 1 = k + 3 := by ring
      have e2 : k + 2 - 1 = k + 1 := by omega
      rw [e1, e2]
      have h1 := ih (k+3) (by omega) (by omega)
      have h2 := leading_unit_monotonicity_length_two_nonneg11 N (k+2)
      have h3 := leading_unit_monotonicity_length_two_nonneg11 N (k+1)
      have hN : (0:ℤ) ≤ (N:ℤ) := by positivity
      nlinarith [mul_nonneg hN h3]

private lemma leading_unit_monotonicity_length_two_P_shift (H : ℕ → ℤ) (n : ℕ) :
    (∑ i ∈ Finset.range (n+3), H (i+1)) =
      (∑ i ∈ Finset.range n, H (i+1)) + H (n+1) + H (n+2) + H (n+3) := by
  rw [show n+3 = (n+2)+1 from rfl, Finset.sum_range_succ]
  rw [show n+2 = (n+1)+1 from rfl, Finset.sum_range_succ]
  rw [Finset.sum_range_succ]

private lemma leading_unit_monotonicity_length_two_gap11 (N : ℕ) (hN1 : 1 ≤ N) (hN2 : N ≤ 2) :
    ∀ k, 1 ≤ k →
      plrs_seq [1,1,N] k ≤ 1 + ∑ i ∈ Finset.range (k-1), plrs_seq [1,1,N] (i+1) := by
  intro k hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, hk with
    | 1, _ =>
      rw [leading_unit_monotonicity_length_two_val11_1]
      simp
    | 2, _ =>
      rw [leading_unit_monotonicity_length_two_val11_2, Finset.sum_range_one,
        leading_unit_monotonicity_length_two_val11_1]
      norm_num
    | 3, _ =>
      rw [leading_unit_monotonicity_length_two_val11_3, Finset.sum_range_succ, Finset.sum_range_one,
        leading_unit_monotonicity_length_two_val11_1, leading_unit_monotonicity_length_two_val11_2]
      norm_num
    | (n+4), _ =>
      rw [show n+4-1 = n+3 from by omega, leading_unit_monotonicity_length_two_P_shift (plrs_seq [1,1,N]) n]
      rw [show n+4 = (n+2)+2 from rfl,
        leading_unit_monotonicity_length_two_rec11 N (n+2) (by omega)]
      have e1 : n+2+1 = n+3 := by ring
      have e2 : n+2-1 = n+1 := by omega
      rw [e1, e2]
      have hPn : 0 ≤ ∑ i ∈ Finset.range n, plrs_seq [1,1,N] (i+1) :=
        Finset.sum_nonneg (fun i _ => leading_unit_monotonicity_length_two_nonneg11 N (i+1))
      have hcases : N = 1 ∨ N = 2 := by omega
      rcases hcases with rfl | rfl
      · norm_num
        nlinarith
      · have hIH := ih (n+1) (by omega) (by omega)
        rw [show n+1-1 = n from rfl] at hIH
        norm_num
        nlinarith

private lemma leading_unit_monotonicity_length_two_aux (H : ℕ → ℤ)
    (hgap : ∀ n, H (n + 1) ≤ 1 + ∑ i ∈ Finset.range n, H (i + 1)) :
    ∀ n t, 1 ≤ t → t ≤ ∑ i ∈ Finset.range n, H (i + 1) →
      ∃ S : Finset ℕ, (∀ i ∈ S, 1 ≤ i) ∧ (∀ i ∈ S, i ≤ n) ∧ ∑ i ∈ S, H i = t := by
  intro n
  induction n with
  | zero =>
    intro t ht1 ht
    simp at ht
    omega
  | succ n ih =>
    intro t ht1 ht
    rw [Finset.sum_range_succ] at ht
    by_cases hcase : t ≤ ∑ i ∈ Finset.range n, H (i + 1)
    · obtain ⟨S, hS1, hSn, hsum⟩ := ih t ht1 hcase
      exact ⟨S, hS1, fun i hi => by have := hSn i hi; omega, hsum⟩
    · push Not at hcase
      have hHle : H (n + 1) ≤ 1 + ∑ i ∈ Finset.range n, H (i + 1) := hgap n
      by_cases heq : t = H (n + 1)
      · refine ⟨{n + 1}, ?_, ?_, ?_⟩
        · intro i hi; simp at hi; omega
        · intro i hi; simp at hi; omega
        · simp [heq]
      · have ht'1 : 1 ≤ t - H (n + 1) := by omega
        have ht'le : t - H (n + 1) ≤ ∑ i ∈ Finset.range n, H (i + 1) := by omega
        obtain ⟨S, hS1, hSn, hsum⟩ := ih (t - H (n + 1)) ht'1 ht'le
        have hnS : n + 1 ∉ S := by
          intro hmem
          have := hSn (n+1) hmem
          omega
        refine ⟨insert (n + 1) S, ?_, ?_, ?_⟩
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · omega
          · exact hS1 i hi
        · intro i hi
          rcases Finset.mem_insert.mp hi with rfl | hi
          · omega
          · have := hSn i hi; omega
        · rw [Finset.sum_insert hnS, hsum]
          omega

private lemma leading_unit_monotonicity_length_two_complete_of_gap (H : ℕ → ℤ)
    (hpos : ∀ i, 1 ≤ i → 1 ≤ H i)
    (hgap : ∀ n, H (n + 1) ≤ 1 + ∑ i ∈ Finset.range n, H (i + 1)) :
    is_complete_sequence H := by
  intro t ht
  have ht0 : 0 ≤ t := by omega
  have hcast : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg ht0
  have hbound : t ≤ ∑ i ∈ Finset.range t.toNat, H (i + 1) := by
    have hle : (t.toNat : ℤ) ≤ ∑ i ∈ Finset.range t.toNat, H (i + 1) := by
      calc (t.toNat : ℤ) = ∑ i ∈ Finset.range t.toNat, (1 : ℤ) := by simp
        _ ≤ ∑ i ∈ Finset.range t.toNat, H (i + 1) := by
            apply Finset.sum_le_sum
            intro i _
            exact hpos (i + 1) (by omega)
    rwa [hcast] at hle
  obtain ⟨S, hS1, _, hsum⟩ := leading_unit_monotonicity_length_two_aux H hgap t.toNat t ht hbound
  exact ⟨S, hS1, hsum⟩

private lemma leading_unit_monotonicity_length_two_complete_11 (N : ℕ) (hN1 : 1 ≤ N) (hN2 : N ≤ 2) :
    is_complete_sequence (plrs_seq [1,1,N]) := by
  apply leading_unit_monotonicity_length_two_complete_of_gap
  · exact leading_unit_monotonicity_length_two_pos11 N
  · intro m
    have h := leading_unit_monotonicity_length_two_gap11 N hN1 hN2 (m+1) (by omega)
    rwa [show m+1-1 = m from rfl] at h

/-- Leading-unit monotonicity for coefficient lists of length 2. -/
theorem leading_unit_monotonicity_length_two (N : ℕ) (hN : 1 ≤ N)
    (hcomp : is_complete_sequence (plrs_seq [1, N])) :
    is_complete_sequence (plrs_seq [1, 1, N]) := by
  have hN2 : N ≤ 2 := leading_unit_monotonicity_length_two_le_two_of_complete N hcomp
  exact leading_unit_monotonicity_length_two_complete_11 N hN hN2
