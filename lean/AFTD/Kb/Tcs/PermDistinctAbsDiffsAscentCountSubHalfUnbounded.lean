import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetNatCardMulSuccLeTwoMulSumOfPos
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.FinsetNatMulCardMulSuccLeTwoMulSum
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# perm_distinct_abs_diffs_ascent_count_sub_half_unbounded

Topic: combinatorics   Node: 8bd7f9094763

Provenance: formalization of a published result. Source: arXiv:2610.15860 (A note on the Slater–Vélez permutation), Lemma 1.

For any permutation (a_n) of the positive integers whose consecutive absolute differences are pairwise distinct, A(X) − X/2 is unbounded above, where A(X) counts the v ≤ X whose successor in the sequence is larger than v.
-/

theorem perm_distinct_abs_diffs_ascent_count_sub_half_unbounded (a : ℕ → ℕ)
    (hinj : Function.Injective a) (hpos : ∀ n, 0 < a n) (hsurj : ∀ v, 0 < v → ∃ n, a n = v)
    (hd : Function.Injective (fun n => Int.natAbs ((a (n + 1) : ℤ) - a n))) :
    ∀ C : ℝ, ∃ X : ℕ,
      C < (({v | 1 ≤ v ∧ v ≤ X ∧ ∃ n, a n = v ∧ v < a (n + 1)} : Set ℕ).ncard : ℝ) - X / 2 := open Finset in by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨C, hC⟩ := hcon
  set asc : ℕ → Prop := fun v => ∃ n, a n = v ∧ v < a (n + 1) with hasc
  set Af : ℕ → Finset ℕ := fun X => (Icc 1 X).filter asc with hAf
  have hA : ∀ X, ((Af X).card : ℝ) - X / 2 ≤ C := by
    intro X
    have : ({v | 1 ≤ v ∧ v ≤ X ∧ ∃ n, a n = v ∧ v < a (n + 1)} : Set ℕ).ncard = (Af X).card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext v
      simp [hAf, hasc, and_assoc]
    rw [← this]
    exact hC X
  -- index, successor and difference of a value
  have hidx : ∀ v, ∃ n, 0 < v → a n = v := by
    intro v
    by_cases hv : 0 < v
    · obtain ⟨n, hn⟩ := hsurj v hv
      exact ⟨n, fun _ => hn⟩
    · exact ⟨0, fun h => absurd h hv⟩
  choose idx hidx using hidx
  set s : ℕ → ℕ := fun v => a (idx v + 1) with hs
  set dd : ℕ → ℕ := fun v => Int.natAbs ((a (idx v + 1) : ℤ) - a (idx v)) with hdd
  have hs_pos : ∀ v, 0 < s v := fun v => hpos _
  have hidx_inj : ∀ v w, 0 < v → 0 < w → idx v = idx w → v = w := by
    intro v w hv hw h
    rw [← hidx v hv, ← hidx w hw, h]
  have hs_inj : ∀ v w, 0 < v → 0 < w → s v = s w → v = w := by
    intro v w hv hw h
    exact hidx_inj v w hv hw (Nat.succ_injective (hinj h))
  have hdd_inj : ∀ v w, 0 < v → 0 < w → dd v = dd w → v = w := by
    intro v w hv hw h
    exact hidx_inj v w hv hw (hd h)
  have hasc_iff : ∀ v, 0 < v → (asc v ↔ v < s v) := by
    intro v hv
    constructor
    · rintro ⟨n, hn, hlt⟩
      have : n = idx v := hinj (hn.trans (hidx v hv).symm)
      subst this
      exact hlt
    · intro h
      exact ⟨idx v, hidx v hv, h⟩
  have hs_ne : ∀ v, 0 < v → s v ≠ v := by
    intro v hv h
    have : a (idx v + 1) = a (idx v) := by rw [hidx v hv]; exact h
    exact absurd (hinj this) (Nat.succ_ne_self _)
  have hdd_pos : ∀ v, 0 < v → 0 < dd v := by
    intro v hv
    have := hs_ne v hv
    simp only [hs] at this
    simp only [hdd, Int.natAbs_pos]
    rw [hidx v hv]
    omega
  have hdesc : ∀ v, 0 < v → ¬ asc v → s v + dd v = v := by
    intro v hv hn
    rw [hasc_iff v hv] at hn
    have h1 : a (idx v) = v := hidx v hv
    simp only [hs, hdd] at hn ⊢
    rw [h1]
    omega
  have hascd : ∀ v, 0 < v → asc v → s v + dd v = v + 2 * dd v := by
    intro v hv ha
    rw [hasc_iff v hv] at ha
    have h1 : a (idx v) = v := hidx v hv
    simp only [hs, hdd] at ha ⊢
    rw [h1]
    omega
  -- infinitely many ascents
  have hinf : ∀ M, ∃ v, M < v ∧ asc v := by
    intro M
    by_contra hno
    push_neg at hno
    -- after the indices of the values ≤ M, the sequence only descends
    set N := ∑ v ∈ Icc 1 M, (idx v + 1) with hN
    have hbig : ∀ n, N ≤ n → M < a n := by
      intro n hn
      by_contra hle
      push_neg at hle
      have hv : a n ∈ Icc 1 M := mem_Icc.2 ⟨hpos n, hle⟩
      have : idx (a n) = n := hinj (hidx (a n) (hpos n))
      have h2 : idx (a n) + 1 ≤ N := single_le_sum (f := fun v => idx v + 1)
        (fun _ _ => Nat.zero_le _) hv
      omega
    have hdec : ∀ n, N ≤ n → a (n + 1) < a n := by
      intro n hn
      have h1 := hno (a n) (hbig n hn)
      have h2 : ¬ a n < a (n + 1) := fun h => h1 ⟨n, rfl, h⟩
      have h3 : a (n + 1) ≠ a n := fun h => absurd (hinj h) (Nat.succ_ne_self n)
      omega
    have hdesc' : ∀ j, a (N + j) + j ≤ a N := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have := hdec (N + j) (Nat.le_add_right _ _)
        have e : N + (j + 1) = N + j + 1 := by omega
        rw [e]
        omega
    have := hdesc' (a N + 1)
    omega
  have hgrow : ∀ m, ∃ Y, m ≤ (Af Y).card := by
    intro m
    induction m with
    | zero => exact ⟨0, Nat.zero_le _⟩
    | succ m ih =>
      obtain ⟨Y, hY⟩ := ih
      obtain ⟨v, hv, hav⟩ := hinf Y
      refine ⟨v, ?_⟩
      have hsub : insert v (Af Y) ⊆ Af v := by
        intro w hw
        rcases mem_insert.1 hw with rfl | hw
        · simp only [hAf, mem_filter, mem_Icc]
          exact ⟨⟨by omega, le_rfl⟩, hav⟩
        · simp only [hAf, mem_filter, mem_Icc] at hw ⊢
          exact ⟨⟨hw.1.1, by omega⟩, hw.2⟩
      have hvn : v ∉ Af Y := by
        simp only [hAf, mem_filter, mem_Icc]
        omega
      have := card_le_card hsub
      rw [card_insert_of_notMem hvn] at this
      omega
  set C₀ := ⌈C⌉₊ with hC₀
  obtain ⟨Y, hY⟩ := hgrow C₀
  set F := Af Y with hF
  set E := 2 * ∑ v ∈ F, dd v with hE
  set X := Y + 2 * E + 1 with hX
  set P := (Icc (Y + 1) X).filter asc with hP
  set Q := Icc 1 X \ P with hQ
  have hPsub : P ⊆ Icc 1 X := by
    intro v hv
    simp only [hP, mem_filter, mem_Icc] at hv
    exact mem_Icc.2 ⟨by omega, hv.1.2⟩
  have hpq : P.card + Q.card = X := by
    rw [hQ, card_sdiff_of_subset hPsub]
    have := card_le_card hPsub
    simp only [Nat.card_Icc] at this ⊢
    omega
  have hsum : ∑ v ∈ P, v + ∑ v ∈ Q, v = ∑ v ∈ Icc 1 X, v := by
    rw [hQ, add_comm]
    exact sum_sdiff hPsub
  have hgauss : ∀ X : ℕ, 2 * ∑ v ∈ Icc 1 X, v = X * (X + 1) := by
    intro X
    induction X with
    | zero => simp
    | succ X ih =>
      rw [sum_Icc_succ_top (by omega), mul_add, ih]
      ring
  -- the ascents above `Y`
  have hP_rank : ∀ v ∈ P, 2 * (P.filter (· ≤ v)).card ≤ v := by
    intro v hv
    have hv' := hv
    simp only [hP, mem_filter, mem_Icc] at hv'
    have hsplit : Af v = F ∪ P.filter (· ≤ v) := by
      ext w
      simp only [hAf, hF, hP, mem_union, mem_filter, mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        by_cases hw : w ≤ Y
        · exact Or.inl ⟨⟨h1, hw⟩, h3⟩
        · exact Or.inr ⟨⟨⟨by omega, by omega⟩, h3⟩, h2⟩
      · rintro (⟨⟨h1, h2⟩, h3⟩ | ⟨⟨⟨h1, _⟩, h3⟩, h4⟩)
        · exact ⟨⟨h1, by omega⟩, h3⟩
        · exact ⟨⟨by omega, h4⟩, h3⟩
    have hdisj : Disjoint F (P.filter (· ≤ v)) := by
      rw [disjoint_left]
      intro w hw1 hw2
      simp only [hAf, hF, hP, mem_filter, mem_Icc] at hw1 hw2
      omega
    have hcardv : (Af v).card = F.card + (P.filter (· ≤ v)).card := by
      rw [hsplit, card_union_of_disjoint hdisj]
    have h1 := hA v
    rw [hcardv] at h1
    have h2 : C ≤ (C₀ : ℝ) := Nat.le_ceil C
    have h3 : ((C₀ : ℕ) : ℝ) ≤ (F.card : ℝ) := by exact_mod_cast hY
    push_cast at h1
    have : (2 * (P.filter (· ≤ v)).card : ℝ) ≤ v := by linarith
    exact_mod_cast this
  have hP_sum := finset_nat_mul_card_mul_succ_le_two_mul_sum 2 P hP_rank
  -- the rest
  have hQpos : ∀ v ∈ Q, 0 < v := by
    intro v hv
    simp only [hQ, mem_sdiff, mem_Icc] at hv
    omega
  have hQ_s : Q.card * (Q.card + 1) ≤ 2 * ∑ v ∈ Q, s v := by
    have hinjQ : Set.InjOn s Q := fun v hv w hw h => hs_inj v w (hQpos v hv) (hQpos w hw) h
    have := finset_nat_card_mul_succ_le_two_mul_sum_of_pos (Q.image s) (by
      intro w hw
      obtain ⟨v, _, rfl⟩ := mem_image.1 hw
      exact hs_pos v)
    rwa [card_image_of_injOn hinjQ, sum_image hinjQ] at this
  have hQ_d : Q.card * (Q.card + 1) ≤ 2 * ∑ v ∈ Q, dd v := by
    have hinjQ : Set.InjOn dd Q := fun v hv w hw h => hdd_inj v w (hQpos v hv) (hQpos w hw) h
    have := finset_nat_card_mul_succ_le_two_mul_sum_of_pos (Q.image dd) (by
      intro w hw
      obtain ⟨v, hv, rfl⟩ := mem_image.1 hw
      exact hdd_pos v (hQpos v hv))
    rwa [card_image_of_injOn hinjQ, sum_image hinjQ] at this
  have hQ_sd : ∑ v ∈ Q, (s v + dd v) ≤ ∑ v ∈ Q, v + E := by
    have h1 : ∀ v ∈ Q, s v + dd v ≤ v + (if v ∈ F then 2 * dd v else 0) := by
      intro v hv
      by_cases ha : asc v
      · have hvF : v ∈ F := by
          simp only [hQ, hP, mem_sdiff, mem_filter, mem_Icc, not_and] at hv
          simp only [hF, hAf, mem_filter, mem_Icc]
          refine ⟨⟨hv.1.1, ?_⟩, ha⟩
          by_contra hlt
          exact hv.2 ⟨by omega, hv.1.2⟩ ha
        rw [if_pos hvF, hascd v (hQpos v hv) ha]
      · rw [hdesc v (hQpos v hv) ha]
        omega
    calc ∑ v ∈ Q, (s v + dd v) ≤ ∑ v ∈ Q, (v + (if v ∈ F then 2 * dd v else 0)) :=
          sum_le_sum h1
      _ = ∑ v ∈ Q, v + ∑ v ∈ Q, (if v ∈ F then 2 * dd v else 0) := sum_add_distrib
      _ ≤ ∑ v ∈ Q, v + E := by
          gcongr
          rw [sum_ite_mem, hE, mul_sum]
          exact sum_le_sum_of_subset_of_nonneg inter_subset_right (fun _ _ _ => Nat.zero_le _)
  have hG := hgauss X
  rw [sum_add_distrib] at hQ_sd
  have key : X ≤ 2 * E := by
    have e1 : (P.card : ℤ) + Q.card = X := by exact_mod_cast hpq
    have e2 : (2 : ℤ) * (∑ v ∈ P, v + ∑ v ∈ Q, v : ℕ) = X * (X + 1) := by
      rw [hsum]; exact_mod_cast hG
    have e3 : (((2 * (P.card * (P.card + 1)) : ℕ) : ℤ)) ≤ ((2 * ∑ v ∈ P, v : ℕ) : ℤ) :=
      Nat.cast_le.2 hP_sum
    push_cast at e3
    have e4 : (Q.card : ℤ) * (Q.card + 1) ≤ 2 * ∑ v ∈ Q, (s v : ℤ) := by exact_mod_cast hQ_s
    have e5 : (Q.card : ℤ) * (Q.card + 1) ≤ 2 * ∑ v ∈ Q, (dd v : ℤ) := by exact_mod_cast hQ_d
    have e6 : ((∑ v ∈ Q, s v + ∑ v ∈ Q, dd v : ℕ) : ℤ) ≤ ((∑ v ∈ Q, v + E : ℕ) : ℤ) :=
      Nat.cast_le.2 hQ_sd
    push_cast at e6
    push_cast at e2
    nlinarith [sq_nonneg ((P.card : ℤ) - Q.card)]
  omega
