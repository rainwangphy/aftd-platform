import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampNumberNegTwoOfOddMemOfSt

/-!
# postage_stamp_number_neg_two_of_odd_family_1

Topic: elementary_number_theory   Node: 70257815e9cc

Provenance: helper lemma. arXiv:2610.19470 (Positivity and negativity for h-bases for N), Theorem 4.1 and its proof

For m ≥ 2 with m ≢ 2 (mod 3), the set {-1, 2, m} (2m+1)-fold covers [0, m² + 4m] = [0, n_h(2) - 2].
-/

theorem postage_stamp_number_neg_two_of_odd_family_1 (m : ℕ) (hm : 2 ≤ m) (hm3 : m % 3 ≠ 2) :
    ∀ n : ℕ, n ≤ m ^ 2 + 4 * m + 2 - 2 → int_mem_h_fold_sumset (2 * m + 1)
      {-(1 : ℤ), (1 : ℤ) + 1, (m : ℤ) + 1 - 1} (n : ℤ) := by
  intro n hn
  have key : ∀ s t : ℕ, s + t ≤ 2 * m + 1 →
      (n : ℤ) = ((2 * m + 1 : ℕ) : ℤ) * (-(1 : ℤ)) + (s : ℤ) * (((1 : ℤ) + 1) - (-(1 : ℤ))) +
        (t : ℤ) * (((m : ℤ) + 1 - 1) - (-(1 : ℤ))) →
      int_mem_h_fold_sumset (2 * m + 1) {-(1 : ℤ), (1 : ℤ) + 1, (m : ℤ) + 1 - 1} (n : ℤ) := by
    intro s t hst he
    rw [he]; exact postage_stamp_number_neg_two_of_odd_mem_of_st _ _ _ _ s t hst
  set T := n + 1 * (2 * m + 1) with hTdef
  set q := T / (m + 1) with hq
  set ρ := T % (m + 1) with hρ
  have hTq : (m + 1) * q + ρ = T := Nat.div_add_mod T (m + 1)
  have hρm : ρ < m + 1 := Nat.mod_lt T (by omega)
  have hTZ : ((n : ℕ) : ℤ) + 1 * (2 * (m : ℤ) + 1) = ((m : ℤ) + 1) * (q : ℤ) + (ρ : ℤ) := by
    have : ((T : ℕ) : ℤ) = (((m + 1) * q + ρ : ℕ) : ℤ) := by rw [hTq]
    rw [hTdef] at this; push_cast at this; linarith
  have hnd : n + 2 ≤ m ^ 2 + 4 * m + 2 := by
    have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  have hTq' : (m + 1) * q + ρ + 2 ≤ m ^ 2 + 4 * m + 2 + 1 * (2 * m + 1) := by omega
  have hTq'' : 1 * (2 * m + 1) ≤ (m + 1) * q + ρ := by omega
  have h1 : q ≤ m + 4 := by
    by_contra hc; push Not at hc
    have : (m + 1) * (m + 4 + 1) ≤ (m + 1) * q := Nat.mul_le_mul_left _ hc
    nlinarith
  have h2 : q = m + 4 → ρ + 3 ≤ m := by
    intro hqe
    rw [hqe] at hTq'
    nlinarith
  have h3 : 1 ≤ q := by
    by_contra hc; push Not at hc
    have : (m + 1) * q ≤ (m + 1) * 0 := Nat.mul_le_mul_left _ (by omega)
    nlinarith
  have h4 : q = 1 → m ≤ ρ + 0 := by
    intro hqe
    rw [hqe] at hTq''
    nlinarith
  have h2' : q < m + 4 ∨ ρ + 3 ≤ m := by
    rcases Nat.lt_or_ge q (m + 4) with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (h2 (by omega))
  have h4' : 1 < q ∨ m ≤ ρ + 0 := by
    rcases Nat.lt_or_ge 1 q with hlt | hge
    · exact Or.inl hlt
    · exact Or.inr (h4 (by omega))
  clear h2 h4
  rcases (show m % 3 = 0 ∨ m % 3 = 1 by omega) with hmr | hmr
  · rcases (show ρ % 3 = 0 ∨ ρ % 3 = 1 ∨ ρ % 3 = 2 by omega) with hr | hr | hr
    · have hs : 3 * ((ρ + 0 * (m + 1)) / 3) = ρ + 0 * (m + 1) := by omega
      have hsZ : (3:ℤ) * (((ρ + 0 * (m + 1)) / 3 : ℕ) : ℤ) = (ρ:ℤ) + 0 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 0 : ℕ) : ℤ) = (q:ℤ) - 0 := by
        rw [Nat.cast_sub (show 0 ≤ q by omega)]; norm_num
      refine key ((ρ + 0 * (m + 1)) / 3) (q - 0) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 3 * ((ρ + 2 * (m + 1)) / 3) = ρ + 2 * (m + 1) := by omega
      have hsZ : (3:ℤ) * (((ρ + 2 * (m + 1)) / 3 : ℕ) : ℤ) = (ρ:ℤ) + 2 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 2 : ℕ) : ℤ) = (q:ℤ) - 2 := by
        rw [Nat.cast_sub (show 2 ≤ q by omega)]; norm_num
      refine key ((ρ + 2 * (m + 1)) / 3) (q - 2) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 3 * ((ρ + 1 * (m + 1)) / 3) = ρ + 1 * (m + 1) := by omega
      have hsZ : (3:ℤ) * (((ρ + 1 * (m + 1)) / 3 : ℕ) : ℤ) = (ρ:ℤ) + 1 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 1 : ℕ) : ℤ) = (q:ℤ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ q by omega)]; norm_num
      refine key ((ρ + 1 * (m + 1)) / 3) (q - 1) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
  · rcases (show ρ % 3 = 0 ∨ ρ % 3 = 1 ∨ ρ % 3 = 2 by omega) with hr | hr | hr
    · have hs : 3 * ((ρ + 0 * (m + 1)) / 3) = ρ + 0 * (m + 1) := by omega
      have hsZ : (3:ℤ) * (((ρ + 0 * (m + 1)) / 3 : ℕ) : ℤ) = (ρ:ℤ) + 0 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 0 : ℕ) : ℤ) = (q:ℤ) - 0 := by
        rw [Nat.cast_sub (show 0 ≤ q by omega)]; norm_num
      refine key ((ρ + 0 * (m + 1)) / 3) (q - 0) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 3 * ((ρ + 1 * (m + 1)) / 3) = ρ + 1 * (m + 1) := by omega
      have hsZ : (3:ℤ) * (((ρ + 1 * (m + 1)) / 3 : ℕ) : ℤ) = (ρ:ℤ) + 1 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 1 : ℕ) : ℤ) = (q:ℤ) - 1 := by
        rw [Nat.cast_sub (show 1 ≤ q by omega)]; norm_num
      refine key ((ρ + 1 * (m + 1)) / 3) (q - 1) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
    · have hs : 3 * ((ρ + 2 * (m + 1)) / 3) = ρ + 2 * (m + 1) := by omega
      have hsZ : (3:ℤ) * (((ρ + 2 * (m + 1)) / 3 : ℕ) : ℤ) = (ρ:ℤ) + 2 * ((m:ℤ) + 1) := by
        exact_mod_cast hs
      have htZ : ((q - 2 : ℕ) : ℤ) = (q:ℤ) - 2 := by
        rw [Nat.cast_sub (show 2 ≤ q by omega)]; norm_num
      refine key ((ρ + 2 * (m + 1)) / 3) (q - 2) (by omega) ?_
      rw [htZ]; push_cast
      push_cast at hsZ
      linear_combination hTZ - hsZ
