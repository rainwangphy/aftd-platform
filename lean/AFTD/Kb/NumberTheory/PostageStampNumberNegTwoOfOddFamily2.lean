import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddMemOfSt

/-!
# postage_stamp_number_neg_two_of_odd_family_2

Topic: elementary_number_theory   Node: cda2aacea533

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

For m ≥ 5 with m ≡ 5 (mod 6) and m ≢ 4 (mod 5), the set {-2, 3, m-1} (2m+1)-fold covers [0, m² + 4m - 1] = [0, n_h(2) - 3].
-/

theorem postage_stamp_number_neg_two_of_odd_family_2 (m : ℕ) (hm : 5 ≤ m) (hm6 : m % 6 = 5) (hm5 : m % 5 ≠ 4) :
    ∀ n : ℕ, n ≤ m ^ 2 + 4 * m + 2 - 3 → int_mem_h_fold_sumset (2 * m + 1)
      {-(2 : ℤ), (2 : ℤ) + 1, (m : ℤ) + 1 - 2} (n : ℤ) := by
  intro n hn
  have key : ∀ s t : ℕ, s + t ≤ 2 * m + 1 →
      (n : ℤ) = ((2 * m + 1 : ℕ) : ℤ) * (-(2 : ℤ)) + (s : ℤ) * (((2 : ℤ) + 1) - (-(2 : ℤ))) +
        (t : ℤ) * (((m : ℤ) + 1 - 2) - (-(2 : ℤ))) →
      int_mem_h_fold_sumset (2 * m + 1) {-(2 : ℤ), (2 : ℤ) + 1, (m : ℤ) + 1 - 2} (n : ℤ) := by
    intro s t hst he
    rw [he]; exact postage_stamp_number_neg_two_of_odd_mem_of_st _ _ _ _ s t hst
  set T := n + 2 * (2 * m + 1) with hTdef
  set q := T / (m + 1) with hq
  set ρ := T % (m + 1) with hρ
  have hTq : (m + 1) * q + ρ = T := Nat.div_add_mod T (m + 1)
  have hρm : ρ < m + 1 := Nat.mod_lt T (by omega)
  have hTZ : ((n : ℕ) : ℤ) + 2 * (2 * (m : ℤ) + 1) = ((m : ℤ) + 1) * (q : ℤ) + (ρ : ℤ) := by
    have : ((T : ℕ) : ℤ) = (((m + 1) * q + ρ : ℕ) : ℤ) := by rw [hTq]
    rw [hTdef] at this; push_cast at this; linarith
  have hnd : n + 3 ≤ m ^ 2 + 4 * m + 2 := by
    have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hTq' : (m + 1) * q + ρ + 3 ≤ m ^ 2 + 4 * m + 2 + 2 * (2 * m + 1) := by omega
  have hTq'' : 2 * (2 * m + 1) ≤ (m + 1) * q + ρ := by omega
  have h1 : q ≤ m + 6 := by
    by_contra hc; push Not at hc
    have : (m + 1) * (m + 6 + 1) ≤ (m + 1) * q := Nat.mul_le_mul_left _ hc
    nlinarith
  have h2 : q = m + 6 → ρ + 5 ≤ m := by
    intro hqe
    rw [hqe] at hTq'
    nlinarith
  have h3 : 3 ≤ q := by
    by_contra hc; push Not at hc
    have : (m + 1) * q ≤ (m + 1) * 2 := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have h4 : q = 3 → m ≤ ρ + 1 := by
    intro hqe
    rw [hqe] at hTq''
    nlinarith
  have h2' : q < m + 6 ∨ ρ + 5 ≤ m := by
    rcases Nat.lt_or_ge q (m + 6) with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (h2 (by omega))
  have h4' : 3 < q ∨ m ≤ ρ + 1 := by
    rcases Nat.lt_or_ge 3 q with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (h4 (by omega))
  clear h2 h4
  rcases (show m % 5 = 0 ∨ m % 5 = 1 ∨ m % 5 = 2 ∨ m % 5 = 3 by omega) with hmr | hmr | hmr | hmr
  · rcases (show ρ % 5 = 0 ∨ ρ % 5 = 1 ∨ ρ % 5 = 2 ∨ ρ % 5 = 3 ∨ ρ % 5 = 4 by omega) with hr | hr | hr | hr | hr
    · have hs : 5 * ((ρ + 0 * (m + 1)) / 5) = ρ + 0 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 0 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 0 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 0 : ℕ) : ℤ) = (q:ℤ) - 0 := by
        rw [Nat.cast_sub (show 0 ≤ q by omega)]; norm_num
      refine key ((ρ + 0 * (m + 1)) / 5) (q - 0) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 4 * (m + 1)) / 5) = ρ + 4 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 4 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 4 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 4 : ℕ) : ℤ) = (q:ℤ) - 4 := by
        rw [Nat.cast_sub (show 4 ≤ q by omega)]; norm_num
      refine key ((ρ + 4 * (m + 1)) / 5) (q - 4) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 3 * (m + 1)) / 5) = ρ + 3 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 3 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 3 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 3 : ℕ) : ℤ) = (q:ℤ) - 3 := by
        rw [Nat.cast_sub (show 3 ≤ q by omega)]; norm_num
      refine key ((ρ + 3 * (m + 1)) / 5) (q - 3) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 2 * (m + 1)) / 5) = ρ + 2 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 2 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 2 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 2 : ℕ) : ℤ) = (q:ℤ) - 2 := by
        rw [Nat.cast_sub (show 2 ≤ q by omega)]; norm_num
      refine key ((ρ + 2 * (m + 1)) / 5) (q - 2) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 1 * (m + 1)) / 5) = ρ + 1 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 1 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 1 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 1 : ℕ) : ℤ) = (q:ℤ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ q by omega)]; norm_num
      refine key ((ρ + 1 * (m + 1)) / 5) (q - 1) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
  · rcases (show ρ % 5 = 0 ∨ ρ % 5 = 1 ∨ ρ % 5 = 2 ∨ ρ % 5 = 3 ∨ ρ % 5 = 4 by omega) with hr | hr | hr | hr | hr
    · have hs : 5 * ((ρ + 0 * (m + 1)) / 5) = ρ + 0 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 0 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 0 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 0 : ℕ) : ℤ) = (q:ℤ) - 0 := by
        rw [Nat.cast_sub (show 0 ≤ q by omega)]; norm_num
      refine key ((ρ + 0 * (m + 1)) / 5) (q - 0) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 2 * (m + 1)) / 5) = ρ + 2 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 2 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 2 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 2 : ℕ) : ℤ) = (q:ℤ) - 2 := by
        rw [Nat.cast_sub (show 2 ≤ q by omega)]; norm_num
      refine key ((ρ + 2 * (m + 1)) / 5) (q - 2) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 4 * (m + 1)) / 5) = ρ + 4 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 4 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 4 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 4 : ℕ) : ℤ) = (q:ℤ) - 4 := by
        rw [Nat.cast_sub (show 4 ≤ q by omega)]; norm_num
      refine key ((ρ + 4 * (m + 1)) / 5) (q - 4) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 1 * (m + 1)) / 5) = ρ + 1 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 1 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 1 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 1 : ℕ) : ℤ) = (q:ℤ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ q by omega)]; norm_num
      refine key ((ρ + 1 * (m + 1)) / 5) (q - 1) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 3 * (m + 1)) / 5) = ρ + 3 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 3 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 3 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 3 : ℕ) : ℤ) = (q:ℤ) - 3 := by
        rw [Nat.cast_sub (show 3 ≤ q by omega)]; norm_num
      refine key ((ρ + 3 * (m + 1)) / 5) (q - 3) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
  · rcases (show ρ % 5 = 0 ∨ ρ % 5 = 1 ∨ ρ % 5 = 2 ∨ ρ % 5 = 3 ∨ ρ % 5 = 4 by omega) with hr | hr | hr | hr | hr
    · have hs : 5 * ((ρ + 0 * (m + 1)) / 5) = ρ + 0 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 0 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 0 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 0 : ℕ) : ℤ) = (q:ℤ) - 0 := by
        rw [Nat.cast_sub (show 0 ≤ q by omega)]; norm_num
      refine key ((ρ + 0 * (m + 1)) / 5) (q - 0) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 3 * (m + 1)) / 5) = ρ + 3 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 3 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 3 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 3 : ℕ) : ℤ) = (q:ℤ) - 3 := by
        rw [Nat.cast_sub (show 3 ≤ q by omega)]; norm_num
      refine key ((ρ + 3 * (m + 1)) / 5) (q - 3) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 1 * (m + 1)) / 5) = ρ + 1 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 1 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 1 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 1 : ℕ) : ℤ) = (q:ℤ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ q by omega)]; norm_num
      refine key ((ρ + 1 * (m + 1)) / 5) (q - 1) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 4 * (m + 1)) / 5) = ρ + 4 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 4 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 4 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 4 : ℕ) : ℤ) = (q:ℤ) - 4 := by
        rw [Nat.cast_sub (show 4 ≤ q by omega)]; norm_num
      refine key ((ρ + 4 * (m + 1)) / 5) (q - 4) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 2 * (m + 1)) / 5) = ρ + 2 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 2 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 2 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 2 : ℕ) : ℤ) = (q:ℤ) - 2 := by
        rw [Nat.cast_sub (show 2 ≤ q by omega)]; norm_num
      refine key ((ρ + 2 * (m + 1)) / 5) (q - 2) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
  · rcases (show ρ % 5 = 0 ∨ ρ % 5 = 1 ∨ ρ % 5 = 2 ∨ ρ % 5 = 3 ∨ ρ % 5 = 4 by omega) with hr | hr | hr | hr | hr
    · have hs : 5 * ((ρ + 0 * (m + 1)) / 5) = ρ + 0 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 0 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 0 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 0 : ℕ) : ℤ) = (q:ℤ) - 0 := by
        rw [Nat.cast_sub (show 0 ≤ q by omega)]; norm_num
      refine key ((ρ + 0 * (m + 1)) / 5) (q - 0) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 1 * (m + 1)) / 5) = ρ + 1 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 1 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 1 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 1 : ℕ) : ℤ) = (q:ℤ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ q by omega)]; norm_num
      refine key ((ρ + 1 * (m + 1)) / 5) (q - 1) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 2 * (m + 1)) / 5) = ρ + 2 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 2 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 2 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 2 : ℕ) : ℤ) = (q:ℤ) - 2 := by
        rw [Nat.cast_sub (show 2 ≤ q by omega)]; norm_num
      refine key ((ρ + 2 * (m + 1)) / 5) (q - 2) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 3 * (m + 1)) / 5) = ρ + 3 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 3 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 3 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 3 : ℕ) : ℤ) = (q:ℤ) - 3 := by
        rw [Nat.cast_sub (show 3 ≤ q by omega)]; norm_num
      refine key ((ρ + 3 * (m + 1)) / 5) (q - 3) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 5 * ((ρ + 4 * (m + 1)) / 5) = ρ + 4 * (m + 1) := by omega
      have hsZ : (5:ℤ) * (((ρ + 4 * (m + 1)) / 5 : ℕ) : ℤ) = (ρ:ℤ) + 4 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 4 : ℕ) : ℤ) = (q:ℤ) - 4 := by
        rw [Nat.cast_sub (show 4 ≤ q by omega)]; norm_num
      refine key ((ρ + 4 * (m + 1)) / 5) (q - 4) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
