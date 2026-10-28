import AFTD.Prelude
import AFTD.Kb.Tcs.IsKstCode
import AFTD.Kb.Tcs.KstCodeMaxDensity
import AFTD.Kb.Tcs.KstCodeCardLe
import AFTD.Kb.Tcs.IsKstCodeEvenEdgeGraphs
import AFTD.Kb.Tcs.NcardEvenEdgeGraphs

/-!
# kst_code_density_odd_odd

Topic: combinatorics   Node: 2b08f230b860

Provenance: formalization of a published result. Source: arXiv:2610.35136, Sharp Bounds for Graph-Codes Avoiding Complete Bipartite Differences, Proposition 3.2

Let s and t be odd natural numbers, and let n be a natural number such that s + t ≤ n. Then the maximum density of a K_{s,t}-code in simple graphs on vertex set [n], kst_code_max_density s t n, is equal to 1/2.
-/

/-- The maximum density of a K_{s,t}-code on Fin n is exactly 1/2 when s and t are odd and n ≥ s + t. -/
theorem kst_code_density_odd_odd (s t n : ℕ) (hs : Odd s) (ht : Odd t) (hn : s + t ≤ n) :
    kst_code_max_density s t n = 1 / 2 := by
  classical
  have hs1 : 1 ≤ s := by obtain ⟨k, rfl⟩ := hs; omega
  have ht1 : 1 ≤ t := by obtain ⟨k, rfl⟩ := ht; omega
  have hn2 : 2 ≤ n := by omega
  have h_le : ∀ C : Set (SimpleGraph (Fin n)),
      (⨆ (_hC : is_kst_code s t n C), (Set.ncard C : ℝ) / (2 ^ (n.choose 2) : ℝ)) ≤ 1 / 2 := by
    intro C
    by_cases h : is_kst_code s t n C
    · rw [ciSup_pos h]
      have hcard_C := kst_code_card_le s t n hs1 ht1 hn C h
      have hk : 1 ≤ n.choose 2 := Nat.choose_pos hn2
      have hk' : n.choose 2 = (n.choose 2 - 1) + 1 := by omega
      have hpow : (2 ^ (n.choose 2) : ℝ) = (2 ^ (n.choose 2 - 1) : ℝ) * 2 := by
        conv_lhs => rw [hk']
        rw [pow_succ]
      have hpos : (0 : ℝ) < (2 ^ (n.choose 2) : ℝ) := by positivity
      rw [div_le_iff₀ hpos, hpow]
      have hcast : (Set.ncard C : ℝ) ≤ (2 ^ (n.choose 2 - 1) : ℝ) := by
        exact_mod_cast hcard_C
      linarith
    · rw [ciSup_neg h, Real.sSup_empty]
      norm_num
  apply le_antisymm
  · dsimp [kst_code_max_density]
    have : Nonempty (Set (SimpleGraph (Fin n))) := ⟨∅⟩
    exact ciSup_le h_le
  · dsimp [kst_code_max_density]
    set C_even : Set (SimpleGraph (Fin n)) := {G | Even G.edgeFinset.card}
    have hC_even : is_kst_code s t n C_even := is_kst_code_even_edge_graphs s t n hs ht
    have hcard : C_even.ncard = 2 ^ (n.choose 2 - 1) := ncard_even_edge_graphs n hn2
    have hdens : (C_even.ncard : ℝ) / (2 ^ (n.choose 2) : ℝ) = 1 / 2 := by
      rw [hcard]
      have hk : 1 ≤ n.choose 2 := Nat.choose_pos hn2
      have hk' : n.choose 2 = (n.choose 2 - 1) + 1 := by omega
      have hpow : (2 ^ (n.choose 2) : ℝ) = (2 ^ (n.choose 2 - 1) : ℝ) * 2 := by
        conv_lhs => rw [hk']
        rw [pow_succ]
      rw [Nat.cast_pow, Nat.cast_ofNat, hpow]
      have hne : ((2 : ℝ) ^ (n.choose 2 - 1)) ≠ 0 := by positivity
      nth_rw 1 [← one_mul ((2 : ℝ) ^ (n.choose 2 - 1))]
      rw [mul_comm ((2 : ℝ) ^ (n.choose 2 - 1)) 2]
      exact mul_div_mul_right 1 2 hne
    have hinner : (⨆ (_hC : is_kst_code s t n C_even), (C_even.ncard : ℝ) / (2 ^ (n.choose 2) : ℝ)) = 1 / 2 := by
      rw [ciSup_pos hC_even, hdens]
    rw [← hinner]
    have hbdd : BddAbove (Set.range fun C : Set (SimpleGraph (Fin n)) =>
        ⨆ (_hC : is_kst_code s t n C), (C.ncard : ℝ) / (2 ^ (n.choose 2) : ℝ)) := by
      use 1 / 2
      rintro y ⟨C, rfl⟩
      dsimp only
      exact h_le C
    exact le_ciSup hbdd C_even
